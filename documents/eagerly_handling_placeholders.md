# Eagerly Handling Placeholders

> [!NOTE]  
>
> This document is largely an artefact of history rather than something useful to read. It was written
> before any implementation on -Zassumptions-on-binders had began and was largely used to try and sketch
> out what we were trying to do as an initial impl and get thoughts down on paper. This has not been
> updated since and likely contains dated/incorrect information and is not a very pleasant read.

## Initial Impl Plan

Only handle things inside the trait solver. Higher Ranked Relate during HIR typeck and MIR typeck will still yield outlives involving placeholders.

We also will not check assumptions when instantiating binders. This means we won't fix any of the soundness bugs but it will make implementation significantly easier

When entering a binder universally we will compute its list of assumptions by looking at the contained data and computing region constraints required for well formedness.

We will then push this list of constraints to a mapping in the InferCtxt from universe to assumptions involving that universes placeholders.

When leak checking (inside of the trait solver) we will destructure type outlives constraints involving placeholders into SolverVerifies.

When leak checking we take the (new) set of SolverVerifies in the InferCtxt and remove the placeholders from the SolverVerify. We do this by looking at the list of assumptions on a given placeholder, and rewriting the SolverVerify to require constraints on the assumptions. E.g.

If we have a goal `'!a_U2: 'c` and we have an assumption `'!a_U2: 'b_U1` then when leak checking U2 we would create a VerifyBound of `'!b_U1: 'c => 'a_U2: 'c`.

Then when leak checking `U1` we would look at the assumptions on `'!b_U1`. If there are none then this VerifyBound does not hold and we would return `NoSolution`. If there are some, e.g. `'b_U1: 'd` and `'b_U1: 'e` then we would rewrite this VerifyBound into
`Any('d: 'c, 'e: 'c) => '!a_U2: 'c`.

At each leak checking step we handle all placeholders by either:
- Rewriting VerifyBound's to no longer talk of the placeholder
- Return NoSolution because the VerifyBound does not hold
- Stall with ambiguity in some cases(?) which cases?

In theory we likely also want to implement some evaluation relation for VerifyBounds which does not result in a final yes/no, and instead can be used to "simplify" the VerifyBounds. This is probably good for performance as we would avoid passing around very large VerifyBounds across canonical queries.

We probably dont actually want to use VerifyBound in the solver because it needs to be extended in weird ways (see later section on rewrite rules)

---

There are 4 operations we need:
1. Given a term produce the set of region constraints required for it to be well formed
    - used to compute the assumptions of a binder
2. Destructure a TypeOutlives into a VerifyBound from inside the trait solver
3. Rewrite a SolverVerify to no longer use placeholders in a specific universe
    - used to avoid needing to propagate assumptions on placeholders all the way to the root universe
    - rewriting should remove terms which are satisfied or unsatisfiable 
4. SolverVerify evaluation relation.
    - used to simplify SolverVerifys which is useful for performance
    - used to eagerly produce region errors? i.e. the point of leak checking
    - I guess this is more of a "simplification" pass and actual evaluation happens as part of removing placeholders from the solver verify

---

We would like to avoid depending on RegionOutlives and TypeOutlives assumptions in the environment *other* than from assumptions on binders entered as part of the current goal.

Not doing so likely has very bad caching implications as it would require extending the ParamEnv with implied region bounds from binders.

## Computing implied bounds

What are we supposed to do with region constraints produced as part of assumptions computation? I.e. as a result of normalizing stuff. 

It's unsound to create assumptions from before normalization until lowering creates actual WF assumptions which can be checked by callers. However, we do just kinda eagerly normalize everywhere so the min impl should just be unsound here and consider normalized forms for implied bounds :thinking_face: 

Avoids weird jank due to getting implied bounds sometimes and othertimes not due to current states of inference :woman-shrugging: 

Are there problems with deriving assumptions on a binder in a defining scope then passing it to a caller and getting less assumptions needing to be checked?

```rust
fn defines_opaque<'a, 'b: 'a'>() -> for<'a1, 'b2> fn() -> Tait<'a1, 'b1> {
    let _: PhantomData<&'a &'b ()> = PhantomData::<Tait<'a, 'b>>; 
    
    for<'a1, 'b1> || -> Tait<'a1, 'b1> {
        // depend on `'a1: 'b1` here somehow? i do not
        // know how implied bounds on closures works exactly :3
        
        // I guess this is actually the same problem as defining
        // scopes with stronger where clauses than the opaque.
        // That potentially applying from turning implicit implied
        // bounds explicit is *scary* from a back compat POV though.
    }
}

fn caller() {
    // callable without ever proving `'b: 'a`?
    let a: for<'a, 'b> fn() -> Tait<'a, 'b> = defines_opaque();
}
```

how do implied bounds on closures work lol:
```rust
#![feature(type_alias_impl_trait, closure_lifetime_binder)]

type Foo<'a, 'b> = impl Sized;

#[define_opaque(Foo)]
fn foo() -> for<'a, 'b> fn(&'a (), &'b ()) -> Foo<'a, 'b> {
    for<'a, 'b> |_: &'a (), _: &'b ()| -> &'a &'b () { &&() }
    //~^ ERROR: 'b: 'a doesn't hold
}
```

do we just only compute closure implied bounds from argument types unlike with functions?

## Rewrite Rules

Vb\(G, R) => G: R

1. Vb = IfEq(for<> vb_t vb_r)
    - see below
2. Vb = '!a_U2: 'x
    - 'x is outlived by `'!a_U2` if 'x is outlived by any of the assumptions on the placeholder
    - ``Any(outlived_regions('!a_U2)[n]: 'x)``
3. Vb = 'x: !a_U2
    - doesn't currently exist but may be necessary to support rewriting IfEqs into lower universes
    - 'x outlives '!a_U2 if it outlives any region known to outlive `!a_U2`
    - ``Any('x: outlived_by_regions('!a_U2)[n])``
4. G = Alias<'!a_U2, Foo<'!a_U2>> (within G)
    - only used by `IfEq` which we can rewrite to not care about the placeholders in the wrong universe
5. R = '!a_U2 (as R)
    - by supporting arbitrary region constraints in VerifyBounds we can rewrite an R in U2 to an OR constraint of any regions in U1 (see cases 2 and 3)

### IfEq

solver verifies with placeholders in G are scary. G is only relevant insofar as evaluating IfEq verify bounds cares about G.
```
assumptions: 'a_U1: 'b_U1
             'b_U1: 'a_U1
             the above assumptions are not knowable as they are in
             a lower universe than the verify is currently in
             'c_U2: 'd_U2
             
             
verify U2:   g  = Alias<'a_U1, 'c_U2>
             r  = 'c_U2
             vb = g = Alias<'b_U1, 'c_U2 and r: 'd_U2
```

Unless we pass down assumptions from U1 to U2 we cant determine that the IfEq holds. Maybe we can handle determining if two placeholders are equal via bidirectional outlives and then pick the lowest bound var placeholder as the representative one?

Alternatively we can rewrite the above by checking equalities of things in U2 and keeping the lower universe equalities unchecked. E.g. rewrite the above to:
```
assumptions: 'a_U1: 'b_U1
             'b_U1: 'a_U1
             'c_U2: 'd_U2

verify U2:   g = * (g is not important anymore)
             r = 'c_U2
             vb = All(
                'b_U1: 'a_U1,
                'a_U1: 'b_U1,
                r: 'd_U2,
             )

```

This would require VerifyBounds handling arbitrary region constraints not just `'x: r`. See later for how to handle rewriting `'x: 'd_U2` to a lower universe, or `'d_U2: 'x`.

An example for this would require proving `Alias<'!a_U1, 'c_U2>: 'c_U2` with no item bounds and an asssumption in the env of `Alias<'!b_U1, 'c_U2>: 'c_U2`.

```rust
impl<'a, 'c> Trait for Alias<'a, 'c>
where
    Alias<'a, 'c>: 'c
{
    type Assoc = ();        
}

for<'a: 'b, 'b: 'a> fn(for<'c> fn(
        &'c Alias<'b, 'c>,
        <Alias<'a, 'c> as Trait>::Assoc,
    )
)
```

if we were to, for example, wf check `<Alias<'a, 'c> as Trait>::Assoc`. We would have the assumptions `'a: 'b, 'b: 'a, Alias<'b, 'c>: 'c`, and be trying to check that `Alias<'a, 'c>: 'c` holds.

The VerifyBound for this would include a IfEq as in the example verify bounds above.

## Future Work

Introduce a `PredicateKind::HigherRankedRelate` (or equivalent) then move equating of higher ranked types into the trait solver so that we eagerly handle placeholders there too.

Replace uses of opaques involving placeholders in a defining scope with higher ranked uses, e.g. rewrite `Opaque<'!a> := &'!a u32` to `for<'a> Opaque<'a' := &'a u32>`. Avoids leaking placeholders out of a binder via the opaque type storage.

Prove assumptions when instantiating binders existentially. This should fix #25860.

Use new leak check during coherence too. Trying to make VerifyBound rewriting complete and sound seems non trivial and may be simpler to drop the completeness requirement for now:tm:?