import ModalDistribution.Logic.Properties.Quorums
import ModalDistribution.Logic.Properties.Modalities
import ModalDistribution.Logic.Properties.Sequentiality

/-!
# Modal logic properties (Sections 4 and 5)

This file re-exports the logical infrastructure from Sections 4 and 5 of the HBB
paper. The implementation has been split into modular subfiles for better organization:

- `Properties.Quorums`: QuorumFamily structure and quorum intersection lemmas
- `Properties.Modalities`: Diamond/box modality lemmas and duality properties
- `Properties.Sequentiality`: Sequentiality modality lemmas and sequential reasoning

This reorganization maintains backward compatibility - all definitions and lemmas
are still accessible via `ModalDistribution.Logic.Properties`.
-/

-- All definitions and lemmas are automatically available through the imports above
