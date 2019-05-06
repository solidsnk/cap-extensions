## Capability machine extensions for temporal safety

### Directory Structure

src/Op/Sourcesyntax.agda : Syntax of ImpR
src/Op/SourceSemantics.agda : Ideal semantics of ImpR
src/Op/DirectCap.agda : Capability semantics of ImpR w/o the extensions
src/Op/DirectCapEx.agda : Capability semantics of ImpR with the extensions
src/Op/DirectCap/Properties.agda : Insecurity of the capability semantics
src/Op/DirectCapEx/Properties.agda : Various properties
src/Op/DirectCapEx/Bisim.agda : Proof that the state relation is a bisimulation
src/Op/DirectCapEx/FA.aga : Proof of full abstraction

Tested for Agda version 2.6.0. Requires agda-stdlib (included).
