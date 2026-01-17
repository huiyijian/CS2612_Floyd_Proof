# Floyd Algorithm Level 4 - Path Reconstruction Proof Plan

## 🎯 Objective
Extend Floyd algorithm to record predecessor information and prove that reconstructed paths are indeed shortest paths.

---

## 📊 Current Status Analysis

### ✅ Completed (Level 2 & 3)
- Main theorem `Floyd_correct`: Proves `distance_correct`
- Loop invariant: `Floyd_loop_invariant done s`
- Key lemma `shortest_path_last_edge`: Proves edge membership in shortest paths
- Core helper lemmas in `floyd.v` (~2000 lines)

### 🔍 What Level 4 Needs
1. **State Extension**: Add predecessor information
2. **Algorithm Modification**: Update predecessors during relaxation
3. **Path Reconstruction**: Build path from predecessor chain
4. **Correctness Proof**: Prove reconstructed paths are shortest

---

## 🗂️ Phase 1: State & Algorithm Extension

### Step 1.1: Extend State Definition
**File**: `algorithms/Floyd/Floyd.v` (line ~70)

**Current**:
```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;
}.
```

**New**:
```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;
  pred: (V * V) -> option V;  (* Predecessor: pred[u][v] = intermediate vertex *)
}.

Instance: Settable St := settable! mkSt <dist; pred>.
```

**Rationale**: 
- `pred[u][v] = Some k` means the shortest path from u to v goes through k
- `pred[u][v] = None` means direct edge or unreachable

---

### Step 1.2: Modify Relaxation Operation
**File**: `algorithms/Floyd/Floyd.v` (line ~77)

**Current**:
```coq
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (Z_op_min (dist0 (i, j)) 
                (Z_op_plus (dist0 (i, k)) (dist0 (k, j)))); dist0 |>).
```

**New**:
```coq
Definition update_dist_with_pred (i j k: V): program St unit :=
  update' (fun s =>
    let new_dist := Z_op_plus (s.(dist) (i, k)) (s.(dist) (k, j)) in
    if Z_op_lt new_dist (s.(dist) (i, j)) then
      s <| dist ::= (i, j) !-> new_dist; 
           pred ::= (i, j) !-> Some k |>
    else s).
```

**Key Decision**: Need to define `Z_op_lt` (strict less-than for option Z)

---

### Step 1.3: Update Floyd Algorithm Definition
**File**: `algorithms/Floyd/Floyd.v` (line ~81-90)

Replace `update_dist` with `update_dist_with_pred` in:
- `Floyd_j`
- Keep `Floyd_k` and `Floyd` unchanged (they just call Floyd_j)

---

## 🔨 Phase 2: Path Reconstruction Function

### Step 2.1: Define Path Reconstruction
**File**: New section in `algorithms/Floyd/Floyd.v` (after line ~140)

```coq
(** Path reconstruction from predecessor information *)
Fixpoint reconstruct_path_aux 
  (pred: (V * V) -> option V) (u v: V) (fuel: nat) : option (list V) :=
  match fuel with
  | O => None  (* Ran out of fuel - cycle detected *)
  | S n =>
    match pred (u, v) with
    | None => 
        (* Direct path: check if u = v or there's direct edge *)
        if V_eq_dec u v then Some [u]
        else Some [u; v]  (* Assume direct edge exists if pred = None *)
    | Some k =>
        (* Path goes through k: u → k → v *)
        match reconstruct_path_aux pred u k n with
        | None => None
        | Some path_uk =>
            match reconstruct_path_aux pred k v n with
            | None => None
            | Some path_kv =>
                Some (path_uk ++ (tail path_kv))  (* Avoid duplicating k *)
            end
        end
    end
  end.

Definition reconstruct_path (pred: (V * V) -> option V) (u v: V) : option (list V) :=
  reconstruct_path_aux pred u v (num_vertices g).  (* Use graph size as fuel *)
```

**Design Choices**:
1. Use fuel (bounded recursion) to ensure termination
2. Return `option (list V)` - vertex sequence
3. Handle direct edges vs intermediate vertices

---

### Step 2.2: Convert Vertex List to Path Object
**File**: `algorithms/Floyd/Floyd.v`

```coq
(** Convert vertex list to path object P *)
Fixpoint vertices_to_path (vlist: list V) : option P :=
  match vlist with
  | [] => None
  | [v] => Some (empty_path v)
  | u :: v :: rest =>
      (* Need edge from u to v *)
      match find_edge g u v with
      | None => None
      | Some e =>
          match vertices_to_path (v :: rest) with
          | None => None
          | Some p_rest => Some (concat_path (single_path u v e) p_rest)
          end
      end
  end.

(** Complete reconstruction *)
Definition reconstruct_full_path (s: St) (u v: V) : option P :=
  match reconstruct_path s.(pred) u v with
  | None => None
  | Some vlist => vertices_to_path vlist
  end.
```

**Challenge**: Need `find_edge : G -> V -> V -> option E` (may require graph library extension)

---

## 📐 Phase 3: Specification & Invariants

### Step 3.1: Extended Loop Invariant
**File**: `algorithms/Floyd/Floyd.v` (after line ~114)

```coq
(** Extended invariant: dist + pred consistency *)
Definition Floyd_loop_invariant_with_pred (done: V -> Prop) (s: St): Prop :=
  (* Part 1: Distance correctness (unchanged) *)
  (forall u v, min_weight_distance_in_vset g u v done (s.(dist) (u, v))) /\
  
  (* Part 2: Predecessor consistency *)
  (forall u v k, 
    s.(pred) (u, v) = Some k ->
    (* k is in the intermediate vertex set *)
    k ∈ done /\
    (* The path u → k → v equals the shortest path u → v *)
    s.(dist) (u, v) = Z_op_plus (s.(dist) (u, k)) (s.(dist) (k, v))) /\
  
  (* Part 3: None predecessor means direct or unreachable *)
  (forall u v,
    s.(pred) (u, v) = None ->
    (u = v) \/ (exists e, step_aux g e u v) \/ (s.(dist) (u, v) = None)).
```

---

### Step 3.2: Path Reconstruction Correctness
**File**: `algorithms/Floyd/Floyd.v`

```coq
(** Specification: reconstructed path is shortest *)
Definition path_reconstruction_correct (s: St): Prop :=
  forall u v p,
    reconstruct_full_path s u v = Some p ->
    min_weight_path g u v p.

(** Main Level 4 Specification *)
Definition level4_correct (s: St): Prop :=
  distance_correct s /\  (* Level 2 *)
  path_reconstruction_correct s.  (* Level 4 *)
```

---

## 🔬 Phase 4: Key Lemmas

### Lemma 4.1: Relaxation Preserves Invariant
```coq
Lemma update_with_pred_correct:
  forall i j k done s,
    Floyd_loop_invariant_with_pred done s ->
    k ∈ done ->
    Floyd_loop_invariant_with_pred done (update_dist_with_pred i j k s).
```

**Proof Sketch**:
1. Case analysis on whether relaxation happens
2. If relaxed: use `shortest_path_last_edge` (Level 3 lemma!)
3. If not: invariant preserved trivially

---

### Lemma 4.2: Reconstruction Produces Valid Path
```coq
Lemma reconstruct_path_valid:
  forall s u v vlist,
    Floyd_loop_invariant_with_pred (fun _ => True) s ->
    reconstruct_path s.(pred) u v = Some vlist ->
    exists p, vertices_to_path vlist = Some p /\ path_valid g p.
```

**Proof Strategy**:
- Induction on fuel
- Use predecessor consistency from invariant
- Show each segment is valid path

---

### Lemma 4.3: Reconstructed Path Weight Equals Distance
```coq
Lemma reconstructed_path_weight:
  forall s u v p,
    Floyd_loop_invariant_with_pred (fun _ => True) s ->
    reconstruct_full_path s u v = Some p ->
    path_weight g p = s.(dist) (u, v).
```

**Proof Strategy**:
- Induction on reconstruction structure
- Use: `s.(dist) (u, v) = s.(dist) (u, k) + s.(dist) (k, v)` from invariant
- Use: `path_weight (concat p1 p2) = weight p1 + weight p2`

---

### Lemma 4.4: Reconstructed Path is Shortest
```coq
Lemma reconstructed_path_is_shortest:
  forall s u v p,
    Floyd_loop_invariant_with_pred (fun _ => True) s ->
    distance_correct s ->
    reconstruct_full_path s u v = Some p ->
    min_weight_path g u v p.
```

**Proof Strategy**:
1. Show `path_weight g p = s.(dist) (u, v)` (Lemma 4.3)
2. Show `s.(dist) (u, v)` is minimum distance (from `distance_correct`)
3. Conclude p is shortest path

---

## 🎯 Phase 5: Main Theorem

### Step 5.1: Modified Main Theorem
**File**: `algorithms/Floyd/Floyd.v`

```coq
Theorem Floyd_with_pred_correct:
  Hoare 
    initialized_state_with_pred
    Floyd_with_pred
    (fun _ s => level4_correct s).
Proof.
  unfold Floyd_with_pred.
  eapply Hoare_conseq.
  3: apply (Hoare_forset Floyd_loop_invariant_with_pred).
  - (* Initialization *)
    intros s H. 
    split.
    + exact H.  (* Distance part *)
    + (* Predecessor initialization: all None *)
      intros u v k Hpred. 
      unfold initialized_state_with_pred in H.
      (* Show contradiction or prove property *)
      ...
  - (* Final implication *)
    intros b s Hinv.
    split.
    + (* distance_correct - reuse Level 2 proof *)
      ...
    + (* path_reconstruction_correct *)
      unfold path_reconstruction_correct.
      intros u v p Hrec.
      apply reconstructed_path_is_shortest; assumption.
  - (* Proper morphism *)
    ...
  - (* Loop body correctness *)
    intros done k Hsub Hin Hnotin.
    (* Similar structure to original, but using extended invariant *)
    ...
Qed.
```

---

## 📋 Implementation Checklist

### Phase 1: Code Extension (Est. 1-2 days)
- [ ] 1.1: Extend `St` record with `pred` field
- [ ] 1.2: Define `Z_op_lt` for option Z
- [ ] 1.3: Implement `update_dist_with_pred`
- [ ] 1.4: Update `Floyd_j` to use new update function
- [ ] 1.5: Define `initialized_state_with_pred`

### Phase 2: Reconstruction (Est. 2-3 days)
- [ ] 2.1: Implement `reconstruct_path_aux` with fuel
- [ ] 2.2: Define `reconstruct_path` wrapper
- [ ] 2.3: Implement `find_edge` or use graph library
- [ ] 2.4: Implement `vertices_to_path`
- [ ] 2.5: Define `reconstruct_full_path`

### Phase 3: Specifications (Est. 1 day)
- [ ] 3.1: Define `Floyd_loop_invariant_with_pred`
- [ ] 3.2: Define `path_reconstruction_correct`
- [ ] 3.3: Define `level4_correct`

### Phase 4: Lemmas (Est. 5-7 days)
- [ ] 4.1: Prove `update_with_pred_correct`
- [ ] 4.2: Prove `reconstruct_path_valid`
- [ ] 4.3: Prove `reconstructed_path_weight`
- [ ] 4.4: Prove `reconstructed_path_is_shortest`
- [ ] 4.5: Prove helper lemmas for fuel reasoning
- [ ] 4.6: Prove helper lemmas for vertex list operations

### Phase 5: Main Theorem (Est. 3-4 days)
- [ ] 5.1: State `Floyd_with_pred_correct`
- [ ] 5.2: Prove initialization case
- [ ] 5.3: Prove final implication (using Phase 4 lemmas)
- [ ] 5.4: Prove loop body preservation
- [ ] 5.5: Handle Proper morphism

---

## 🚀 Quick Start Guide

### Step 1: Create Backup
```bash
cd algorithms/Floyd
cp Floyd.v Floyd_level2_backup.v
```

### Step 2: Start with State Extension
Begin modifications at line ~70 in Floyd.v

### Step 3: Test Compilation Incrementally
```bash
make Floyd.vo
```

### Step 4: Utilize Existing Proofs
- Reuse `Floyd_correct` proof structure
- Leverage `shortest_path_last_edge` from Level 3
- Reference helper lemmas from `graph_lib/examples/floyd.v`

---

## ⚠️ Potential Challenges

### Challenge 1: Graph Library Limitations
**Issue**: May not have `find_edge : G -> V -> V -> option E`

**Solutions**:
- Add axiom temporarily: `Axiom find_edge : G -> V -> V -> option E`
- Or extend graph library with this function
- Or use alternative representation (edge list)

### Challenge 2: Termination of Reconstruction
**Issue**: Coq requires all functions to terminate

**Solution**: Use fuel parameter (bounded recursion) with graph size as bound

### Challenge 3: Predecessor Cycles
**Issue**: Malformed predecessor might have cycles

**Mitigation**: 
- Invariant ensures `pred` forms DAG
- Fuel prevents infinite loops
- Return `None` on cycle detection

### Challenge 4: Level 3 Connection
**Issue**: Need to connect `shortest_path_last_edge` to reconstruction

**Strategy**:
- Use this lemma in `update_with_pred_correct`
- Shows that setting `pred[i][j] = k` is valid when relaxation succeeds

---

## 📊 Estimated Effort

| Phase | Estimated Time | Difficulty |
|-------|----------------|------------|
| Phase 1: Extension | 1-2 days | ⭐⭐ |
| Phase 2: Reconstruction | 2-3 days | ⭐⭐⭐ |
| Phase 3: Specs | 1 day | ⭐⭐ |
| Phase 4: Lemmas | 5-7 days | ⭐⭐⭐⭐⭐ |
| Phase 5: Main Theorem | 3-4 days | ⭐⭐⭐⭐ |
| **Total** | **12-17 days** | **⭐⭐⭐⭐** |

---

## 🎓 Learning Resources

### Key Files to Study
1. `algorithms/Floyd/Floyd.v` (lines 246-603): Main theorem structure
2. `graph_lib/examples/floyd.v`: Helper lemmas library
3. `MonadLib/StateRelMonad/`: Hoare logic framework
4. `graph_lib/reachable/path_basic.v`: Path definitions

### Recommended Reading Order
1. Understand current `Floyd_correct` proof
2. Study `shortest_path_last_edge` proof technique
3. Review `concat_path` and `path_weight` properties
4. Explore `Hoare_forset` framework

---

## ✅ Success Criteria

The proof is complete when:
1. ✅ All definitions compile without errors
2. ✅ All lemmas proven (no `Admitted`)
3. ✅ Main theorem `Floyd_with_pred_correct` proven
4. ✅ Can extract OCaml/Haskell code that runs
5. ✅ Documentation explains key proof ideas

---

## 🔄 Iterative Development Strategy

### Iteration 1: Minimal Extension (2-3 days)
- Extend state with `pred`
- Modify update function (may use simplified version)
- Get basic compilation working

### Iteration 2: Reconstruction Logic (3-4 days)
- Implement reconstruction functions
- Prove basic properties (validity, termination)

### Iteration 3: Invariant Strengthening (4-5 days)
- Formalize extended invariant
- Prove preservation through loop

### Iteration 4: Final Theorem (3-4 days)
- Connect all pieces
- Prove main Level 4 theorem

---

## 📝 Notes

- This plan assumes familiarity with existing Level 2 & 3 proofs
- Leverage existing infrastructure maximally
- Ask for help on graph library extensions if needed
- Consider incremental commits to track progress

**Last Updated**: January 14, 2026
**Status**: Plan Ready for Execution
