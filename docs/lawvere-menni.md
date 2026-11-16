# Lawvere and Menni: when is a pre-cohesive morphism locally connected?

**Pre-cohesion: no.** Lawvere and Menni ask after [§10, Corollary 10.4](https://www.tac.mta.ca/tac/volumes/30/26/30-26.pdf#page=22) whether every pre-cohesive geometric morphism is stably pre-cohesive. By that corollary, this is equivalent to asking whether every such morphism is locally connected. We construct a pre-cohesive morphism of presheaf toposes that is not locally connected.

**Cohesion: yes.** Every cohesive geometric morphism between elementary toposes is locally connected, hence stably pre-cohesive. Here *cohesive* means pre-cohesive with Lawvere's Continuity axiom. We do not assume choice, a natural numbers object, or sufficient cohesion. These are theorems about ordinary elementary toposes; an internal Agda development concerning higher types has a different scope, described [separately](../agda/precohesion/README.md).

## Where pre-cohesion fails

Write the adjoints as Π ⊣ Δ ⊣ Γ ⊣ ∇: Π takes pieces, Δ makes objects discrete, Γ takes points, and ∇ makes objects codiscrete. In a pre-cohesive morphism, Δ and ∇ are fully faithful, Π preserves finite products, and the canonical points-to-pieces map ΓX → ΠX is epic. Local connectedness asks for more: for every X → ΔB and A → B, the canonical map from Π(X ×<sub>ΔB</sub> ΔA) to ΠX ×<sub>B</sub> A must be an isomorphism.

Take the category of finite product expressions in the symmetric group S₃ and the cyclic groups C₂ and C₃, with all group homomorphisms between them. Abelianization reflects it into the corresponding abelian subcategory. The reflector preserves products and its units split. It therefore induces a pre-cohesive morphism between the two presheaf toposes. The obstruction is visible in the sign map S₃ → C₂. Its kernel is C₃; abelianizing that kernel still gives C₃. Abelianizing the sign map first gives an isomorphism C₂ → C₂, whose kernel is trivial. These two results cannot agree. The Lean proof carries this failure to the required pullback in the presheaf toposes. The same example fails even monicity of the Continuity comparison, at the representables for S₃ and C₃.

The presheaf construction builds on Richard Garner and Thomas Streicher, [“An essential local geometric morphism which is not locally connected though its inverse image part is an exponential ideal”](https://web.science.mq.edu.au/~rgarner/Papers/GaSt.pdf). The split units in the group example supply the additional Nullstellensatz condition that pre-cohesion requires. The public Lean statements are [the counterexample and its specification](../lean/Counterexample/Main.lean) and [the explicit Continuity witness](../lean/Counterexample/ContinuityWitness.lean).

## Why cohesion suffices

Continuity says that the canonical comparison Π(X<sup>ΔA</sup>) → (ΠX)<sup>A</sup> is an isomorphism for every X and A. The proof constructs a subterminal object P of the base. On the open part defined by P, points and pieces agree: ΓX → ΠX is invertible. On the closed part the restricted morphism remains cohesive and its base is Boolean. The local-connectedness comparison is invertible on both parts, and the two restrictions together detect isomorphisms. This does not require P to have a complement.

The full Lean development proves `Positive.CohesiveMorphism.locallyConnected` and `Positive.CohesiveMorphism.open_closed_decomposition`. Both passed the Lean kernel and their axiom checks; they use only `propext`, `Classical.choice`, and `Quot.sound`. The complete proof imports elementary-topos ports for which we have not established redistribution permission. The public Lean tree includes the entire negative proof and some independent positive lemmas, but does not build these two positive theorems. The implication from local connectedness to stable pre-cohesion is the published Lawvere–Menni equivalence cited above.

## Related weakenings

For comparison, *epi-continuity* asks only that each Continuity comparison be epic. The following further results are stated and proved in the research write-up; the public Lean tree does not provide an end-to-end check of them.

| Earlier result or question | What the argument gives |
| --- | --- |
| Lawvere–Menni, Theorem 9.3 and Corollary 9.4: internal choice under stable connected codiscreteness. | For a sufficiently cohesive pre-cohesive morphism, epi-continuity is equivalent to internal choice in the base. Under these conditions the morphism is locally connected and satisfies stable connected codiscreteness. In particular, for a cohesive morphism, sufficient cohesion already implies internal choice in the base. |
| Lawvere–Menni, remarks after Corollary 6.5 and Lemma 8.6, and Corollary 10.6: does sufficient cohesion imply connected codiscreteness, and does the latter imply its stable form? | Yes to both under epi-continuity: for any pre-cohesive morphism satisfying epi-continuity, over any base, sufficient cohesion, connected codiscreteness, and stable connected codiscreteness are equivalent. No unconditional implication is claimed. |
