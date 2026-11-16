# Precohesion in native Agda

This development asks when taking pieces commutes with changing the base of a family. The [categorical Lawvere–Menni theorem](../../docs/lawvere-menni.md) answers this in ordinary elementary toposes. Here the families are types, the bases are discrete types, and a relative shape comes with its unit and universal property. We supply the shape data for the family in question. We do not derive from the native modalities a reflector defined uniformly for every family.

The sources establish several steps toward stability over discrete **set** bases. They do not yet prove the general stability theorem for arbitrary source families over such bases, or its higher, untruncated analogue.

| Where to start | What Agda checks |
| --- | --- |
| `LocalConnectedness`, `RelativeSliceShape`, `ShapeReindexing` | The data of set-valued pieces, the universal property of a supplied relative shape, and the canonical comparison along a change of discrete base. |
| `NativeSharp`, `NativeFlatIdentity` | The native ♯ modality, and Shulman's Theorem 6.1 identifying paths between boxed points with boxed paths. Neither module requires flat splitting. |
| `FullToShape0`, `ComparisonTransfer` | Given a full relative shape, truncating the **fibres** of its carrier gives the set-fibred interface, with supplied truncation and function extensionality. The comparison for the original input can be recovered from the comparison for its fibrewise set-truncation under the displayed hypotheses. This reduces a problem; it does not prove that the truncated comparison is invertible. |
| `OpenComparison`, `ClosedComparisonProof` | The open comparison is invertible when points-to-pieces is invertible on the two totals. On the closed part, the proof constructs the comparison equivalence from its specified truncation, discrete and closed data, and crisp decisions. |
| `SetSourceKernelStatements`, `SetSourceApplication` | A worked dependent Boolean diagram: a proof of the kernel statement, with the listed hypotheses, yields the comparison at each open crisp point. The kernel proof is an argument to the client; this example does not supply a global stability theorem. |
| `MajoritySet` | A type with a majority operation is a set, assuming just its three majority laws. This independent lemma uses neither cohesion nor additional axioms. |

The build uses [Agda 2.9.0](https://github.com/agda/agda/releases/tag/v2.9.0) and its primitive modules. It needs neither the standard library nor a TypeTopology checkout. All 217 local modules passed the check.

Modules with `--safe` state that restriction in their headers. Some others use `--flat-split`; declaration macros such as `DeclareClosedShape` deliberately introduce an instance of a shape axiom schema for a specified closed family. A successful check of a client means its conclusion follows from the assumptions it imports or lists. See [sources and credits](SOURCES.md) for the prototypes and proofs reworked here.
