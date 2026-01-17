# Floyd-Warshall Formal Proof Progress Summary

## Current Status
- **Goal**: Formally verify the Floyd-Warshall algorithm using Coq.
- **Branch**: `level_4` (created for this phase).
- **Core File**: `algorithms/Floyd/Floyd.v`.

## Completed Components
1. **Basic Invariants**: Defined `Floyd_invariant_general` covering distance (`dist`) and path reconstruction (`next`) correctness.
2. **Helper Lemmas**:
   - `min_dist_stable_k`: Distance stability when adding intermediate node `k`.
   - `min_dist_recur`: Recursive structure of shortest paths.
   - `min_dist_invalid_u` (and variants): Contradiction proofs for invalid vertices.
3. **Hoare Logic Integration**:
   - `Hoare_forset`: Custom Hoare rule for set iteration loops.
   - `Hoare_update'`: State update rules.
   - `Hoare_conseq`: Pre/Postcondition strengthening.
4. **Distance Update Verification**:
   - Implemented `Floyd_invariant_general_ext` to verify state transitions during `update_dist`.
   - Handled `u=i, v=j` update cases and non-update cases.
   - Resolved `t_set` and `t_update_eq` map logic for record updates.

## Ongoing Work & Remaining Tasks
1. **`Floyd_invariant_general_ext` Completion**:
   - **Current Focus**: Verifying the `next` pointer invariant (`Hnext_valid`) in the updated state.
   - **Issue**: Need to prove `Hval_yj` (line ~1785) to ensure `next` points to valid intermediate nodes or destinations.
2. **`Floyd_k_correct`**:
   - Link the loop invariant established in `Floyd_invariant_general_ext` to the overall `Floyd_k` loop.
   - Finalize `Hoare_forset` application arguments.
3. **Empty Path Handling**:
   - Refine `min_weight_distance_in_vset` for empty paths (`empty_path_valid`).
4. **Final Theorem (`Floyd_correct`)**:
   - Combine all lemmas to prove the top-level correctness specification.

## Known Issues (Fixes Applied)
- **Map Update Logic**: Replaced `simpl` with `match goal ... replace` pattern to correctly handle `t_set` unfolding and `EqDec` inference.
- **Type Mismatches**: Fixed `update_dist` type signatures and `Hoare` triple types.
- **Graph Library Dependencies**: Aligned with `graph_lib` path definitions (`destruct_1n_path`, `head_valid`).

## Next Steps for Collaboration
- Continue proof of `Hval_yj` in `Floyd.v`.
- Verify `Floyd_k_correct` integrates cleanly with `Floyd_invariant_general`.
- Run `make` regularly to catch regression errors in `graph_lib` interactions.
