# Critical spectral subspace issues

The findings below were identified and resolved during the round. The finer retuned negative crossing is a mathematical open target, not a defect in an accepted theorem.

## CS-I1: Two displayed expansions lost their additive plus sign

Found during the probability author's separate review of root/graph-resonance-v1.md. Equations (17) and (18) placed O_P(1/m) immediately after the leading expression, omitting the intended plus sign. This is a formula transcription issue. Status: resolved in revision 2. Both graph application reviewers checked the exact delta and accepted the final revision. Revision 1 remains preserved.

## CS-I2: Figure generation used a fallback plotting cache

The first render succeeded but the plotting library reported that its default cache directory was not writable. Status: the generator now selects a dedicated temporary configuration directory before importing the plotting library. A fresh replay passed with syntax warnings treated as errors and an empty standard error stream. All 303 positive formula checks and three negative checks passed. The final figure was visually inspected.

## CS-I3: A figure label abbreviated the constant host direction incorrectly

The positive-resonance annotation said host mass when its value 1/4 refers only to the original host's constant direction. The proofs and mass triples were correct. Status: annotation corrected to name the constant host direction explicitly. The fresh figure passed all 306 formula checks with no standard error output and was visually inspected. The updated dependency record and its consistency check pass. Status: resolved.
