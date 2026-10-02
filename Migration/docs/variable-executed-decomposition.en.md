# Variable executed decomposition

This extension preserves the convergent public instance and its equivalence
between full binary width and injective conservation. It adds executions in
which some outputs group together while others remain distinct.

## Local production

`VariableRelationalExecution` forms both occurrences from the same constituted
state. The action searches for the existing transport at the selected variable.
If the search succeeds, it applies the discovered relation; otherwise, it keeps
the input continuation. Traces index the actual inputs and outputs. Acceptance
preservation on arbitrary continuations is proved separately and consumed by
admission.

The first stage of `MixedExample` produces an image of width one, the second
an image of width two. The four source profiles remain distinct; the composed
image carries two obligations. Failed discovery does not mean that no other
transport is possible: here, the two obligations correspond to outputs actually
proved distinct.

## Composition and successors

`VariableOutputComposition` exactly realizes tuples of stored outputs, with
both return laws. Two profiles have the same obligation exactly when they
produce the same tuple. On these factorized histories, width is the product of
local widths, hence `2^k`, where `k` counts local images of width two. This
number is read after their production, not supplied as an input.

A common tail requires agreement with the assignments actually produced.
`AdaptiveRelationalExecution` separately handles differing tails: each tail is
indexed by the state formed from its occurrence's output. Its mixed example
has six profiles and three distinct outputs. The preceding product formula is
not applied to adaptive trees.

`UnboundedMixedExecution` constructs, for every `count`, a history of
`count + 1` stages from successively produced states. Selection is connected
to candidate extraction from the received residual. Search succeeds on the
grouping prefixes and fails at the separating terminal stage. The source
carrier has `2^(count + 1)` profiles; the image of output tuples has width two.
Acceptance of these tuples follows from the preserving actions.

## Certificate and scope

`PublicExecutionConstitutionCertificate.wholeHeadIsPrefixLocal` incorporates
the existing exactness proof for the entire initial production, regardless of
the remaining horizon. The audited producer is not replaced.

All these constructions are accessible from `import RelationalPerimeter`.
Their regression checks are in `Tests/`. The four foundational files are
unchanged. No total-cost result is added: width, descriptive size, and execution
time remain different quantities.

This extension neither replaces nor silently generalizes the audited target.
It does not establish that the retained obligations are irreducible under every
other preserving transformation. It describes exactly the images of executed
actions and the successors their outputs allow the construction to form.
