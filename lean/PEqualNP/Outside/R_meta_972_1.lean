import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_1
    (h_edge : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[0]? = Option.some g ∧ g.inputs = [(0 : ℕ), (13 : ℕ)]) →
      (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val - 13) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true)) →
      64 ≤ C.size)
    (h_noninc : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[0]? = Option.some g ∧ g.inputs = [(0 : ℕ), (15 : ℕ)]) →
      (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val - 13) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true)) →
      64 ≤ C.size)
    (h_pts : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[0]? = Option.some g ∧ g.inputs = [(0 : ℕ), (1 : ℕ)]) →
      (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val - 13) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true)) →
      64 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  let edges : List (ℕ × ℕ) :=
    [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
     (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
     (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
     (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
     (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
     (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
     (12, 14), (12, 15), (12, 17), (12, 23)]
  let rel : Fin 26 → Fin 26 → Bool := fun u v =>
    (decide (u.val < 13) && decide (13 ≤ v.val) && ((u.val + (v.val - 13)) % 13 == 0 || (u.val + (v.val - 13)) % 13 == 1 || (u.val + (v.val - 13)) % 13 == 3 || (u.val + (v.val - 13)) % 13 == 9)) ||
    (decide (v.val < 13) && decide (13 ≤ u.val) && ((v.val + (u.val - 13)) % 13 == 0 || (v.val + (u.val - 13)) % 13 == 1 || (v.val + (u.val - 13)) % 13 == 3 || (v.val + (u.val - 13)) % 13 == 9))
  have rel_symm : ∀ u v : Fin 26, rel u v = rel v u := by decide +kernel
  have edges_iff : ∀ u v : Fin 26, (u.val, v.val) ∈ edges ↔ u.val < 13 ∧ 13 ≤ v.val ∧ rel u v = true := by
    decide +kernel
  have edges_compact : ∀ u v : Fin 26, (u.val, v.val) ∈ edges ↔ u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val - 13) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide +kernel
  let fwd : List (List ℕ) :=
    [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 25, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
     [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
     [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 21, 22, 18, 17, 23, 20, 15, 16, 19, 24, 25],
     [0, 3, 6, 9, 12, 2, 5, 8, 11, 1, 4, 7, 10, 13, 16, 19, 22, 25, 15, 18, 21, 24, 14, 17, 20, 23]]
  let bwd : List (List ℕ) :=
    [[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13],
     [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
     [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 21, 22, 18, 17, 23, 20, 15, 16, 19, 24, 25],
     [0, 9, 5, 1, 10, 6, 2, 11, 7, 3, 12, 8, 4, 13, 22, 18, 14, 23, 19, 15, 24, 20, 16, 25, 21, 17]]
  let gf : ℕ → Fin 26 → Fin 26 := fun i u => Fin.ofNat 26 ((fwd.getD i []).getD u.val 0)
  let gb : ℕ → Fin 26 → Fin 26 := fun i u => Fin.ofNat 26 ((bwd.getD i []).getD u.val 0)
  let tbl : List ℕ :=
    [0, 0, 1, 3, 3, 1, 2, 3, 2, 3, 2, 3, 0, 0, 3, 0, 2, 2, 3, 3, 3, 2, 0, 3, 3, 1,
     0, 0, 1, 1, 3, 1, 1, 3, 1, 1, 1, 0, 2, 0, 0, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1,
     1, 1, 0, 1, 3, 2, 0, 3, 2, 1, 3, 0, 0, 1, 3, 3, 0, 3, 0, 1, 1, 3, 1, 3, 1, 3,
     3, 1, 1, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 3, 3, 0, 2, 3, 2, 1, 0, 3, 1,
     3, 3, 3, 0, 0, 2, 2, 3, 3, 2, 3, 3, 3, 1, 3, 3, 3, 2, 0, 0, 3, 0, 3, 3, 1, 1,
     1, 1, 2, 0, 2, 0, 2, 2, 2, 3, 0, 0, 0, 3, 0, 0, 0, 0, 2, 2, 2, 2, 1, 1, 3, 1,
     2, 1, 0, 0, 2, 2, 0, 3, 2, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1, 3, 3, 2, 2, 0, 0, 1,
     3, 3, 3, 0, 3, 2, 3, 0, 2, 3, 3, 0, 0, 3, 0, 0, 3, 0, 2, 0, 2, 2, 3, 0, 0, 3,
     2, 1, 2, 2, 3, 2, 2, 2, 0, 0, 3, 3, 0, 1, 2, 2, 2, 2, 3, 0, 2, 0, 2, 3, 3, 3,
     3, 1, 1, 3, 2, 3, 0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 2, 3, 2, 0, 3, 1, 3, 3, 3, 1,
     2, 1, 3, 0, 3, 0, 0, 3, 3, 0, 0, 0, 2, 2, 2, 3, 0, 0, 0, 0, 1, 3, 3, 3, 2, 2,
     3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 2, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 3,
     0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 1, 3, 3, 3, 1, 1, 2, 2, 2, 0, 1, 2, 2, 3, 2, 3, 3, 1, 3, 3, 3, 1,
     3, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 3, 0, 1, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0,
     0, 2, 3, 0, 3, 0, 0, 0, 2, 2, 3, 0, 3, 2, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 2,
     2, 1, 0, 3, 3, 0, 0, 3, 2, 2, 0, 3, 0, 2, 2, 0, 0, 0, 3, 3, 1, 1, 3, 0, 3, 1,
     2, 3, 3, 3, 2, 0, 0, 0, 2, 3, 0, 0, 2, 3, 0, 2, 0, 0, 1, 1, 3, 3, 1, 0, 3, 3,
     3, 2, 0, 0, 0, 2, 1, 2, 3, 2, 0, 3, 0, 2, 0, 2, 3, 1, 0, 1, 2, 1, 3, 3, 2, 0,
     3, 2, 1, 2, 0, 2, 3, 0, 0, 0, 0, 0, 0, 3, 2, 0, 3, 1, 1, 0, 3, 1, 0, 0, 2, 1,
     3, 1, 1, 3, 3, 2, 3, 2, 2, 3, 1, 0, 0, 3, 0, 0, 1, 3, 2, 3, 0, 0, 3, 3, 1, 1,
     2, 1, 3, 2, 0, 2, 2, 2, 0, 1, 3, 0, 0, 1, 2, 1, 1, 3, 1, 1, 0, 0, 2, 0, 2, 1,
     0, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0, 0, 3, 1, 3, 0, 3, 2, 0, 1, 1, 3,
     3, 1, 3, 0, 3, 1, 0, 0, 3, 3, 3, 0, 0, 3, 0, 0, 0, 0, 3, 0, 3, 0, 1, 0, 1, 1,
     3, 3, 1, 3, 1, 3, 0, 0, 3, 3, 2, 3, 0, 3, 0, 0, 3, 3, 2, 2, 1, 2, 1, 1, 0, 1,
     1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3, 0, 1, 0, 2, 1, 3, 0, 1, 1, 1, 3, 1, 1, 0]
  let nxt : Fin 26 → Fin 26 → ℕ := fun a b => tbl.getD (26 * a.val + b.val) 0
  let base : Fin 26 → Fin 26 → Bool := fun a b =>
    (a == 0 && (b == 1 || b == 13 || b == 15)) || (b == 0 && (a == 1 || a == 13 || a == 15))
  let stepP : Fin 26 × Fin 26 → Fin 26 × Fin 26 := fun p =>
    if base p.1 p.2 then p else (gf (nxt p.1 p.2) p.1, gf (nxt p.1 p.2) p.2)
  let reach6 : Fin 26 → Fin 26 → Bool := fun a b =>
    let p := stepP (stepP (stepP (stepP (stepP (stepP (a, b))))))
    base p.1 p.2
  have left_ok : ∀ i : Fin 4, ∀ u : Fin 26, gb i.val (gf i.val u) = u := by decide +kernel
  have right_ok : ∀ i : Fin 4, ∀ u : Fin 26, gf i.val (gb i.val u) = u := by decide +kernel
  have rel_ok : ∀ i : Fin 4, ∀ u v : Fin 26, rel (gf i.val u) (gf i.val v) = rel u v := by decide +kernel
  have nxt_lt : ∀ a b : Fin 26, nxt a b < 4 := by decide +kernel
  have reach_ok : ∀ a b : Fin 26, a ≠ b → reach6 a b = true := by decide +kernel
  have symm_pair : ∀ a b : Fin 26, a ≠ b →
      ∃ φ ψ : Fin 26 → Fin 26, (∀ u, ψ (φ u) = u) ∧ (∀ u, φ (ψ u) = u) ∧
        (∀ u v, rel (φ u) (φ v) = rel u v) ∧
        ((φ a = 0 ∧ (φ b = 1 ∨ φ b = 13 ∨ φ b = 15)) ∨
         (φ b = 0 ∧ (φ a = 1 ∨ φ a = 13 ∨ φ a = 15))) := by
    have step_one : ∀ (p : Fin 26 × Fin 26)
        (h : ∃ φ ψ : Fin 26 → Fin 26, (∀ u, ψ (φ u) = u) ∧ (∀ u, φ (ψ u) = u) ∧
          (∀ u v, rel (φ u) (φ v) = rel u v) ∧ base (φ (stepP p).1) (φ (stepP p).2) = true),
        ∃ φ ψ : Fin 26 → Fin 26, (∀ u, ψ (φ u) = u) ∧ (∀ u, φ (ψ u) = u) ∧
          (∀ u v, rel (φ u) (φ v) = rel u v) ∧ base (φ p.1) (φ p.2) = true := by
      intro p h
      by_cases hb : base p.1 p.2 = true
      · exact ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, hb⟩
      · have hsp : stepP p = (gf (nxt p.1 p.2) p.1, gf (nxt p.1 p.2) p.2) := by simp [stepP, hb]
        rw [hsp] at h
        obtain ⟨φ, ψ, h1, h2, hrel, hbase⟩ := h
        let idx : Fin 4 := ⟨nxt p.1 p.2, nxt_lt p.1 p.2⟩
        refine ⟨fun u => φ (gf idx.val u), gb idx.val ∘ ψ, ?_, ?_, ?_, hbase⟩
        · intro u; simp [h1, left_ok]
        · intro u; simp [right_ok, h2]
        · intro u v; rw [hrel, rel_ok]
    intro a b hab
    have h6 : ∃ φ ψ : Fin 26 → Fin 26, (∀ u, ψ (φ u) = u) ∧ (∀ u, φ (ψ u) = u) ∧
        (∀ u v, rel (φ u) (φ v) = rel u v) ∧ base (φ (stepP (stepP (stepP (stepP (stepP (stepP (a, b))))))).1) (φ (stepP (stepP (stepP (stepP (stepP (stepP (a, b))))))).2) = true :=
      ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, reach_ok a b hab⟩
    obtain ⟨φ, ψ, h1, h2, hrel, hb⟩ :=
      step_one _ (step_one _ (step_one _ (step_one _ (step_one _ (step_one _ h6)))))
    refine ⟨φ, ψ, h1, h2, hrel, ?_⟩
    simpa [base, or_assoc] using hb
  let stepW : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stepW]; omega
  have computes_iff : ∀ (x : Fin 26 → Bool),
      (∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) ↔
      (∃ u v : Fin 26, rel u v = true ∧ x u = true ∧ x v = true) := by
    intro x
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, v, ((edges_iff u v).mp he).2.2, hu, hv⟩
    · rintro ⟨u, v, hrel, hu, hv⟩
      by_cases hu13 : u.val < 13
      · by_cases hv13 : 13 ≤ v.val
        · exact ⟨u, v, (edges_iff u v).mpr ⟨hu13, hv13, hrel⟩, hu, hv⟩
        · have hf : ∀ a b : Fin 26, a.val < 13 → ¬ 13 ≤ b.val → rel a b = false := by decide +kernel
          rw [hf u v hu13 hv13] at hrel; cases hrel
      · by_cases hv13 : v.val < 13
        · exact ⟨v, u, (edges_iff v u).mpr ⟨hv13, by omega, by rwa [rel_symm]⟩, hv, hu⟩
        · have hf : ∀ a b : Fin 26, ¬ a.val < 13 → ¬ b.val < 13 → rel a b = false := by decide +kernel
          rw [hf u v hu13 hv13] at hrel; cases hrel
  have eval_and : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun _ => rfl
  have retarget_eval : ∀ (g0 : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (out w : ℕ) (hw : w < 26 ∨ 26 + gs.length ≤ w)
      (heq : ∀ x : Fin 26 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (List.ofFn x).getD w false),
      let mapW : ℕ → ℕ := fun k => if k < 26 then k else if k = 26 then w else k - 1
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs.map (fun g => ⟨g.op, g.inputs.map mapW⟩), mapW out⟩
      ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn x) := by
    intro g0 gs out w hw heq mapW C' x
    have hsim : ∀ (rem : List PEqualNP.CircuitLowerBounds.Gate) (u v : List Bool),
        u.length + rem.length ≤ 26 + gs.length →
        v.length = u.length + 1 →
        26 ≤ u.length →
        (∀ k, v.getD k false = u.getD (mapW k) false) →
        ∀ k, (rem.foldl stepW v).getD k false =
          ((rem.map fun g => ⟨g.op, g.inputs.map mapW⟩).foldl stepW u).getD (mapW k) false := by
      intro rem
      induction rem with
      | nil =>
        intro u v _ _ _ hmatch k
        simpa using hmatch k
      | cons g rem ih =>
        intro u v hlen hvlen hu26 hmatch k
        simp only [List.map_cons, List.foldl_cons]
        have hbit : g.op.eval (g.inputs.map fun i => v.getD i false) =
            g.op.eval ((g.inputs.map mapW).map fun i => u.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hmatch i
        let b := g.op.eval ((g.inputs.map mapW).map fun i => u.getD i false)
        have hstepu : stepW u ⟨g.op, g.inputs.map mapW⟩ = u ++ [b] := rfl
        have hstepv : stepW v g = v ++ [b] := by simp only [stepW, b]; rw [hbit]
        rw [hstepu, hstepv]
        apply ih (u ++ [b]) (v ++ [b]) (by simp at hlen ⊢; omega) (by simp; omega) (by simp; omega)
        intro m
        by_cases hm26 : m < 26
        · have hmap : mapW m = m := by simp [mapW, hm26]
          rw [hmap, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          simpa [hmap] using hmatch m
        · by_cases hmeq : m = 26
          · subst hmeq
            have hmap : mapW 26 = w := by simp [mapW]
            rw [hmap, List.getD_append _ _ _ _ (by omega)]
            rcases hw with hwlt | hwge
            · rw [List.getD_append _ _ _ _ (by omega)]
              simpa [hmap] using hmatch 26
            · have hgeu : (u ++ [b]).length ≤ w := by simp only [List.length_append, List.length_cons, List.length_nil]; simp only [List.length_cons] at hlen; omega
              rw [List.getD_eq_default _ _ hgeu]
              have hgeu0 : u.length ≤ w := by omega
              have h0 := hmatch 26
              rw [hmap, List.getD_eq_default _ _ hgeu0] at h0
              exact h0
          · have hmap : mapW m = m - 1 := by simp [mapW, hm26, hmeq]
            rw [hmap]
            rcases Nat.lt_trichotomy m v.length with hlt | heqm | hgt
            · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
              simpa [hmap] using hmatch m
            · rw [heqm, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              have hequ : v.length - 1 = u.length := by omega
              rw [hequ, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    change ((gs.map fun g => ⟨g.op, g.inputs.map mapW⟩).foldl stepW (List.ofFn x)).getD (mapW out) false =
      ((g0 :: gs).foldl stepW (List.ofFn x)).getD out false
    rw [List.foldl_cons]
    have hinit : ∀ k, (stepW (List.ofFn x) g0).getD k false = (List.ofFn x).getD (mapW k) false := by
      intro k
      by_cases hk26 : k < 26
      · have hmap : mapW k = k := by simp [mapW, hk26]
        rw [hmap]
        exact List.getD_append _ _ _ _ (by simp; exact hk26)
      · by_cases hkeq : k = 26
        · subst hkeq
          have hmap : mapW 26 = w := by simp [mapW]
          rw [hmap]
          have hlen26 : (List.ofFn x).length = 26 := List.length_ofFn
          simp only [stepW]
          rw [List.getD_append_right _ _ _ _ (by rw [hlen26]), hlen26, Nat.sub_self]
          exact heq x
        · have hmap : mapW k = k - 1 := by simp [mapW, hk26, hkeq]
          rw [hmap]
          have hge1 : (stepW (List.ofFn x) g0).length ≤ k := by simp [stepW]; omega
          have hge0 : (List.ofFn x).length ≤ k - 1 := by simp; omega
          rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge0]
    symm
    exact hsim gs (List.ofFn x) (stepW (List.ofFn x) g0) (by simp) (by simp [stepW]) (by simp) hinit out
  have elimTrue_spec : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ)
      (g0 : PEqualNP.CircuitLowerBounds.Gate) (hg0op : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and) (hg0in : g0.inputs = [])
      (hmono : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (hzero : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn fun _ : Fin 26 => false) = false),
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ gs.length ∧
        ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn x) := by
    intro gs out g0 hg0op hg0in hmono hzero
    let huge : ℕ := 27 + gs.length
    let stepGo : List PEqualNP.CircuitLowerBounds.Gate × List (Option ℕ) → PEqualNP.CircuitLowerBounds.Gate →
        List PEqualNP.CircuitLowerBounds.Gate × List (Option ℕ) := fun st g =>
      let acc := st.1
      let mp := st.2
      let args := g.inputs.map fun i => mp.getD i (Option.some huge)
      PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
        (let kept := args.filterMap id
         if kept.isEmpty then (acc, mp ++ [Option.none])
         else if kept.tail.isEmpty then (acc, mp ++ [Option.some (kept.headD 0)])
         else
           let g' : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, kept⟩
           (acc ++ [g'], mp ++ [Option.some (26 + acc.length)]))
        (if args.any Option.isNone then
           (acc, mp ++ [Option.none])
         else
           let g' : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, args.map (fun o => o.getD huge)⟩
           (acc ++ [g'], mp ++ [Option.some (26 + acc.length)]))
        (acc, mp ++ [Option.none])
        (fun _ => (acc, mp ++ [Option.none]))
        (acc, mp ++ [Option.none])
    let mp0 : List (Option ℕ) := (List.range 26).map Option.some ++ [Option.none]
    let res := gs.foldl stepGo ([], mp0)
    have go_prop : ∀ (rem acc : List PEqualNP.CircuitLowerBounds.Gate) (mp : List (Option ℕ)),
        (∀ g ∈ rem, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ acc, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        acc.length + rem.length ≤ gs.length →
        (∀ o ∈ mp, ∀ w, o = Option.some w → w < 26 + acc.length ∨ huge ≤ w) →
        (∀ x : Fin 26 → Bool, ∀ u : List Bool,
          u.length = mp.length →
          (∀ k, (mp.getD k (Option.some huge) = Option.none → u.getD k false = true) ∧
                (∀ w, mp.getD k (Option.some huge) = Option.some w → u.getD k false = (acc.foldl stepW (List.ofFn x)).getD w false)) →
          (∀ g ∈ (rem.foldl stepGo (acc, mp)).1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
          (rem.foldl stepGo (acc, mp)).1.length ≤ acc.length + rem.length ∧
          (∀ k, ((rem.foldl stepGo (acc, mp)).2.getD k (Option.some huge) = Option.none → (rem.foldl stepW u).getD k false = true) ∧
                (∀ w, (rem.foldl stepGo (acc, mp)).2.getD k (Option.some huge) = Option.some w → (rem.foldl stepW u).getD k false = ((rem.foldl stepGo (acc, mp)).1.foldl stepW (List.ofFn x)).getD w false))) := by
      intro rem
      induction rem with
      | nil =>
        intro acc mp _ hacc _ _ x u _ hinv
        refine ⟨hacc, by simp, ?_⟩
        intro k
        simpa using hinv k
      | cons g rem ih =>
        intro acc mp hrem hacc hlen hmp x u hulen hinv
        have hg := hrem g (by simp)
        have hrem' : ∀ g' ∈ rem, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hrem g' (by simp [hg'])
        have hstep_val : ∀ k, (stepW u g).getD k false =
            if k < u.length then u.getD k false
            else if k = u.length then g.op.eval (g.inputs.map fun i => u.getD i false)
            else false := by
          intro k
          by_cases hk : k < u.length
          · rw [if_pos hk]; exact List.getD_append _ _ _ _ hk
          · rw [if_neg hk]
            by_cases heqk : k = u.length
            · rw [if_pos heqk, heqk]; simp [stepW]
            · rw [if_neg heqk]; exact List.getD_eq_default _ _ (by simp [stepW]; omega)
        have hacc_len : (acc.foldl stepW (List.ofFn x)).length = 26 + acc.length := by
          rw [foldl_len, List.length_ofFn]
        have hhuge : (acc.foldl stepW (List.ofFn x)).getD huge false = false := by
          apply List.getD_eq_default
          rw [hacc_len]
          simp [huge] at hlen ⊢
          omega
        rcases hg.1 with hop | hop
        · rw [List.foldl_cons, List.foldl_cons]
          let args := g.inputs.map fun i => mp.getD i (Option.some huge)
          let kept := args.filterMap id
          have hkept_len : kept.length ≤ g.inputs.length := by
            have h1 := List.length_filterMap_le id args
            simpa [args, kept] using h1
          have hkept_eval : g.op.eval (g.inputs.map fun i => u.getD i false) =
              kept.all (fun w => (acc.foldl stepW (List.ofFn x)).getD w false) := by
            rw [hop, eval_and]
            simp only [List.all_map, Function.comp_apply, id_eq]
            change (g.inputs.all fun i => u.getD i false) = kept.all fun w => (acc.foldl stepW (List.ofFn x)).getD w false
            rw [Bool.eq_iff_iff]
            simp only [List.all_eq_true, kept, args, List.mem_filterMap, id_eq, List.mem_map]
            constructor
            · intro hall w hw
              rcases hw with ⟨o, ⟨i, hi, ho⟩, hwo⟩
              have hi_u := hall i hi
              have hinv_i := (hinv i).2
              cases hwo
              rw [← hinv_i w ho]
              exact hi_u
            · intro hall i hi
              cases hm : mp.getD i (Option.some huge) with
              | none => exact (hinv i).1 hm
              | some w =>
                rw [(hinv i).2 w hm]
                exact hall w ⟨Option.some w, ⟨i, hi, hm⟩, rfl⟩
          cases hkept : kept with
          | nil =>
            have hstep_eq : stepGo (acc, mp) g = (acc, mp ++ [Option.none]) := by
              have hkept' : List.filterMap id (List.map (fun i => mp.getD i (Option.some huge)) g.inputs) = [] := hkept
              dsimp only [stepGo]
              rw [hop]
              dsimp only
              rw [hkept']
              rfl
            rw [hstep_eq]
            have htrue : g.op.eval (g.inputs.map fun i => u.getD i false) = true := by
              rw [hkept_eval, hkept]; rfl
            have hmp' : ∀ o ∈ mp ++ [Option.none], ∀ w, o = Option.some w → w < 26 + acc.length ∨ huge ≤ w := by
              intro o ho w hw
              simp at ho
              rcases ho with ho | rfl
              · exact hmp o ho w hw
              · cases hw
            have hinv' : ∀ k, ((mp ++ [Option.none]).getD k (Option.some huge) = Option.none → (stepW u g).getD k false = true) ∧
                  (∀ w, (mp ++ [Option.none]).getD k (Option.some huge) = Option.some w → (stepW u g).getD k false = (acc.foldl stepW (List.ofFn x)).getD w false) := by
              intro k
              rw [hstep_val k]
              by_cases hk : k < mp.length
              · rw [List.getD_append _ _ _ _ hk, if_pos (by omega)]
                exact hinv k
              · by_cases heqk : k = mp.length
                · subst heqk
                  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
                  rw [if_neg (by omega), if_pos hulen.symm]
                  exact ⟨fun _ => htrue, fun _ hm => (by cases hm)⟩
                · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega), if_neg (by omega)]
                  refine ⟨(fun hm => by cases hm), (fun w hm => by cases hm; exact hhuge.symm)⟩
            have hres := ih acc (mp ++ [Option.none]) hrem' hacc (by simp at hlen ⊢; omega) hmp' x (stepW u g) (by simp [stepW, hulen]) hinv'
            exact ⟨hres.1, by simp at hres ⊢; omega, hres.2.2⟩
          | cons w1 rest =>
            cases hrest : rest with
            | nil =>
              have hstep_eq : stepGo (acc, mp) g = (acc, mp ++ [Option.some w1]) := by
                have hkept' : List.filterMap id (List.map (fun i => mp.getD i (Option.some huge)) g.inputs) = [w1] := by
                  rw [← hrest]; exact hkept
                dsimp only [stepGo]
                rw [hop]
                dsimp only
                rw [hkept']
                rfl
              rw [hstep_eq]
              have hvalw : g.op.eval (g.inputs.map fun i => u.getD i false) = (acc.foldl stepW (List.ofFn x)).getD w1 false := by
                rw [hkept_eval, hkept, hrest]; simp
              have hw1_bound : w1 < 26 + acc.length ∨ huge ≤ w1 := by
                have hmem : w1 ∈ kept := by rw [hkept]; simp
                simp only [kept, args, List.mem_filterMap, id_eq, List.mem_map] at hmem
                rcases hmem with ⟨o, ⟨i, _, ho⟩, rfl⟩
                by_cases hi : i < mp.length
                · rw [List.getD_eq_getElem _ _ hi] at ho
                  exact hmp _ (List.getElem_mem hi) _ ho
                · rw [List.getD_eq_default _ _ (by omega)] at ho
                  cases ho
                  exact Or.inr (le_refl _)
              have hmp' : ∀ o ∈ mp ++ [Option.some w1], ∀ w, o = Option.some w → w < 26 + acc.length ∨ huge ≤ w := by
                intro o ho w hw
                simp at ho
                rcases ho with ho | rfl
                · exact hmp o ho w hw
                · cases hw; exact hw1_bound
              have hinv' : ∀ k, ((mp ++ [Option.some w1]).getD k (Option.some huge) = Option.none → (stepW u g).getD k false = true) ∧
                    (∀ w, (mp ++ [Option.some w1]).getD k (Option.some huge) = Option.some w → (stepW u g).getD k false = (acc.foldl stepW (List.ofFn x)).getD w false) := by
                intro k
                rw [hstep_val k]
                by_cases hk : k < mp.length
                · rw [List.getD_append _ _ _ _ hk, if_pos (by omega)]
                  exact hinv k
                · by_cases heqk : k = mp.length
                  · subst heqk
                    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
                    rw [if_neg (by omega), if_pos hulen.symm]
                    refine ⟨(fun hm => by cases hm), (fun w hm => by cases hm; exact hvalw)⟩
                  · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega), if_neg (by omega)]
                    refine ⟨(fun hm => by cases hm), (fun w hm => by cases hm; exact hhuge.symm)⟩
              have hres := ih acc (mp ++ [Option.some w1]) hrem' hacc (by simp at hlen ⊢; omega) hmp' x (stepW u g) (by simp [stepW, hulen]) hinv'
              exact ⟨hres.1, by simp at hres ⊢; omega, hres.2.2⟩
            | cons w2 rest2 =>
              let g' : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, w1 :: w2 :: rest2⟩
              have hstep_eq : stepGo (acc, mp) g = (acc ++ [g'], mp ++ [Option.some (26 + acc.length)]) := by
                have hkept' : List.filterMap id (List.map (fun i => mp.getD i (Option.some huge)) g.inputs) = w1 :: w2 :: rest2 := by
                  rw [← hrest]; exact hkept
                dsimp only [stepGo]
                rw [hop]
                dsimp only
                rw [hkept']
                rfl
              rw [hstep_eq]
              have hg'_ok : g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 := by
                refine ⟨Or.inl rfl, ?_⟩
                change (w1 :: w2 :: rest2).length ≤ 2
                rw [← hrest, ← hkept]
                exact hkept_len.trans hg.2
              have hacc' : ∀ g'' ∈ acc ++ [g'], g''.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g''.inputs.length ≤ 2 := by
                intro g'' hg''
                simp at hg''
                rcases hg'' with hg'' | rfl
                · exact hacc g'' hg''
                · exact hg'_ok
              have hmp' : ∀ o ∈ mp ++ [Option.some (26 + acc.length)], ∀ w, o = Option.some w → w < 26 + (acc ++ [g']).length ∨ huge ≤ w := by
                intro o ho w hw
                simp only [List.mem_append, List.mem_singleton] at ho
                rcases ho with ho | rfl
                · rcases hmp o ho w hw with h1 | h2
                  · exact Or.inl (by simp; omega)
                  · exact Or.inr h2
                · cases hw; exact Or.inl (by simp)
              have hinv' : ∀ k, ((mp ++ [Option.some (26 + acc.length)]).getD k (Option.some huge) = Option.none → (stepW u g).getD k false = true) ∧
                    (∀ w, (mp ++ [Option.some (26 + acc.length)]).getD k (Option.some huge) = Option.some w → (stepW u g).getD k false = ((acc ++ [g']).foldl stepW (List.ofFn x)).getD w false) := by
                intro k
                have hext : ∀ w, w < 26 + acc.length ∨ huge ≤ w →
                    ((acc ++ [g']).foldl stepW (List.ofFn x)).getD w false = (acc.foldl stepW (List.ofFn x)).getD w false := by
                  intro w hw
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                  rcases hw with hlt | hge
                  · exact List.getD_append _ _ _ _ (by rw [hacc_len]; exact hlt)
                  · have h1 : (stepW (acc.foldl stepW (List.ofFn x)) g').length ≤ w := by
                      simp only [stepW, List.length_append, List.length_cons, List.length_nil]
                      rw [hacc_len]; dsimp only [huge] at hge; omega
                    have h2 : (acc.foldl stepW (List.ofFn x)).length ≤ w := by
                      rw [hacc_len]; dsimp only [huge] at hge; omega
                    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
                rw [hstep_val k]
                by_cases hk : k < mp.length
                · rw [List.getD_append _ _ _ _ hk, if_pos (by omega)]
                  cases hm : mp.getD k (Option.some huge) with
                  | none => refine ⟨fun _ => (hinv k).1 hm, fun _ h2 => by cases h2⟩
                  | some w =>
                    have hwbound : w < 26 + acc.length ∨ huge ≤ w := by
                      rw [List.getD_eq_getElem _ _ hk] at hm
                      exact hmp _ (List.getElem_mem hk) _ hm
                    refine ⟨(fun h2 => by cases h2), fun w' h2 => ?_⟩
                    cases h2
                    rw [hext w hwbound]
                    exact (hinv k).2 w hm
                · by_cases heqk : k = mp.length
                  · subst heqk
                    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
                    rw [if_neg (by omega), if_pos hulen.symm]
                    refine ⟨(fun h2 => by cases h2), fun w h2 => ?_⟩
                    cases h2
                    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                    simp only [stepW]
                    rw [List.getD_append_right _ _ _ _ (by rw [hacc_len]), hacc_len, Nat.sub_self, List.getD_cons_zero]
                    rw [hkept_eval, hkept, hrest]
                    dsimp only [g']
                    rw [eval_and, List.all_map]
                    rfl
                  · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega), if_neg (by omega)]
                    refine ⟨(fun h2 => by cases h2), fun w h2 => ?_⟩
                    cases h2
                    rw [hext huge (Or.inr (le_refl _)), hhuge]
              have hres := ih (acc ++ [g']) (mp ++ [Option.some (26 + acc.length)]) hrem' hacc' (by simp at hlen ⊢; omega) hmp' x (stepW u g) (by simp [stepW, hulen]) hinv'
              exact ⟨hres.1, by simp at hres ⊢; omega, hres.2.2⟩
        · rw [List.foldl_cons, List.foldl_cons]
          let args := g.inputs.map fun i => mp.getD i (Option.some huge)
          by_cases hany : args.any Option.isNone = true
          · have hstep_eq : stepGo (acc, mp) g = (acc, mp ++ [Option.none]) := by
              dsimp only [stepGo]
              rw [hop]
              dsimp only
              exact if_pos hany
            rw [hstep_eq]
            have htrue : g.op.eval (g.inputs.map fun i => u.getD i false) = true := by
              rw [hop, eval_or]
              simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
              simp only [args, List.any_eq_true, List.mem_map] at hany
              rcases hany with ⟨o, ⟨i, hi, ho⟩, hnone⟩
              cases o with
              | none => exact ⟨i, hi, (hinv i).1 ho⟩
              | some _ => simp at hnone
            have hmp' : ∀ o ∈ mp ++ [Option.none], ∀ w, o = Option.some w → w < 26 + acc.length ∨ huge ≤ w := by
              intro o ho w hw
              simp at ho
              rcases ho with ho | rfl
              · exact hmp o ho w hw
              · cases hw
            have hinv' : ∀ k, ((mp ++ [Option.none]).getD k (Option.some huge) = Option.none → (stepW u g).getD k false = true) ∧
                  (∀ w, (mp ++ [Option.none]).getD k (Option.some huge) = Option.some w → (stepW u g).getD k false = (acc.foldl stepW (List.ofFn x)).getD w false) := by
              intro k
              rw [hstep_val k]
              by_cases hk : k < mp.length
              · rw [List.getD_append _ _ _ _ hk, if_pos (by omega)]
                exact hinv k
              · by_cases heqk : k = mp.length
                · subst heqk
                  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
                  rw [if_neg (by omega), if_pos hulen.symm]
                  exact ⟨fun _ => htrue, fun _ hm => by cases hm⟩
                · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega), if_neg (by omega)]
                  refine ⟨(fun hm => by cases hm), (fun w hm => by cases hm; exact hhuge.symm)⟩
            have hres := ih acc (mp ++ [Option.none]) hrem' hacc (by simp at hlen ⊢; omega) hmp' x (stepW u g) (by simp [stepW, hulen]) hinv'
            exact ⟨hres.1, by simp at hres ⊢; omega, hres.2.2⟩
          · let g' : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, args.map fun o => o.getD huge⟩
            have hstep_eq : stepGo (acc, mp) g = (acc ++ [g'], mp ++ [Option.some (26 + acc.length)]) := by
              dsimp only [stepGo]
              rw [hop]
              dsimp only
              exact if_neg hany
            rw [hstep_eq]
            have hg'_ok : g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 := by
              refine ⟨Or.inr rfl, ?_⟩
              simp [g', args, hg.2]
            have hacc' : ∀ g'' ∈ acc ++ [g'], g''.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g''.inputs.length ≤ 2 := by
              intro g'' hg''
              simp at hg''
              rcases hg'' with hg'' | rfl
              · exact hacc g'' hg''
              · exact hg'_ok
            have hmp' : ∀ o ∈ mp ++ [Option.some (26 + acc.length)], ∀ w, o = Option.some w → w < 26 + (acc ++ [g']).length ∨ huge ≤ w := by
              intro o ho w hw
              simp only [List.mem_append, List.mem_singleton] at ho
              rcases ho with ho | rfl
              · rcases hmp o ho w hw with h1 | h2
                · exact Or.inl (by simp; omega)
                · exact Or.inr h2
              · cases hw; exact Or.inl (by simp)
            have hval_g' : g.op.eval (g.inputs.map fun i => u.getD i false) =
                g'.op.eval (g'.inputs.map fun i => (acc.foldl stepW (List.ofFn x)).getD i false) := by
              rw [hop, eval_or]
              dsimp only [g']
              rw [eval_or]
              simp only [args, List.map_map, List.any_map]
              rw [Bool.eq_iff_iff]
              simp only [List.any_eq_true, Function.comp_apply, id_eq]
              constructor
              · rintro ⟨i, hi, hiu⟩
                refine ⟨i, hi, ?_⟩
                cases hm : mp.getD i (Option.some huge) with
                | none =>
                  exfalso
                  apply hany
                  simp only [args, List.any_eq_true, List.mem_map]
                  exact ⟨Option.none, ⟨i, hi, hm⟩, rfl⟩
                | some w =>
                  simp only [hm, Option.getD_some]
                  rw [← (hinv i).2 w hm]
                  exact hiu
              · rintro ⟨i, hi, hiw⟩
                refine ⟨i, hi, ?_⟩
                cases hm : mp.getD i (Option.some huge) with
                | none =>
                  exfalso
                  apply hany
                  simp only [args, List.any_eq_true, List.mem_map]
                  exact ⟨Option.none, ⟨i, hi, hm⟩, rfl⟩
                | some w =>
                  simp only [hm, Option.getD_some] at hiw
                  rw [(hinv i).2 w hm]
                  exact hiw
            have hinv' : ∀ k, ((mp ++ [Option.some (26 + acc.length)]).getD k (Option.some huge) = Option.none → (stepW u g).getD k false = true) ∧
                  (∀ w, (mp ++ [Option.some (26 + acc.length)]).getD k (Option.some huge) = Option.some w → (stepW u g).getD k false = ((acc ++ [g']).foldl stepW (List.ofFn x)).getD w false) := by
              intro k
              have hext : ∀ w, w < 26 + acc.length ∨ huge ≤ w →
                  ((acc ++ [g']).foldl stepW (List.ofFn x)).getD w false = (acc.foldl stepW (List.ofFn x)).getD w false := by
                intro w hw
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                rcases hw with hlt | hge
                · exact List.getD_append _ _ _ _ (by rw [hacc_len]; exact hlt)
                · have h1 : (stepW (acc.foldl stepW (List.ofFn x)) g').length ≤ w := by
                    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
                    rw [hacc_len]; dsimp only [huge] at hge; omega
                  have h2 : (acc.foldl stepW (List.ofFn x)).length ≤ w := by
                    rw [hacc_len]; dsimp only [huge] at hge; omega
                  rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
              rw [hstep_val k]
              by_cases hk : k < mp.length
              · rw [List.getD_append _ _ _ _ hk, if_pos (by omega)]
                cases hm : mp.getD k (Option.some huge) with
                | none => refine ⟨fun _ => (hinv k).1 hm, fun _ h2 => by cases h2⟩
                | some w =>
                  have hwbound : w < 26 + acc.length ∨ huge ≤ w := by
                    rw [List.getD_eq_getElem _ _ hk] at hm
                    exact hmp _ (List.getElem_mem hk) _ hm
                  refine ⟨(fun h2 => by cases h2), fun w' h2 => ?_⟩
                  cases h2
                  rw [hext w hwbound]
                  exact (hinv k).2 w hm
              · by_cases heqk : k = mp.length
                · subst heqk
                  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
                  rw [if_neg (by omega), if_pos hulen.symm]
                  refine ⟨(fun h2 => by cases h2), fun w h2 => ?_⟩
                  cases h2
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                  simp only [stepW]
                  rw [List.getD_append_right _ _ _ _ (by rw [hacc_len]), hacc_len, Nat.sub_self]
                  exact hval_g'
                · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega), if_neg (by omega)]
                  refine ⟨(fun h2 => by cases h2), fun w h2 => ?_⟩
                  cases h2
                  rw [hext huge (Or.inr (le_refl _)), hhuge]
            have hres := ih (acc ++ [g']) (mp ++ [Option.some (26 + acc.length)]) hrem' hacc' (by simp at hlen ⊢; omega) hmp' x (stepW u g) (by simp [stepW, hulen]) hinv'
            exact ⟨hres.1, by simp at hres ⊢; omega, hres.2.2⟩
    have hmp0 : ∀ o ∈ mp0, ∀ w, o = Option.some w → w < 26 + ([] : List PEqualNP.CircuitLowerBounds.Gate).length ∨ huge ≤ w := by
      intro o ho w hw
      simp only [mp0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
      rcases ho with ⟨i, hi, rfl⟩ | rfl
      · cases hw; exact Or.inl (by simp; exact hi)
      · cases hw
    have hinv0 : ∀ x : Fin 26 → Bool, ∀ k,
          (mp0.getD k (Option.some huge) = Option.none → (stepW (List.ofFn x) g0).getD k false = true) ∧
          (∀ w, mp0.getD k (Option.some huge) = Option.some w → (stepW (List.ofFn x) g0).getD k false = (([] : List PEqualNP.CircuitLowerBounds.Gate).foldl stepW (List.ofFn x)).getD w false) := by
      intro x k
      by_cases hk : k < 26
      · have hmk : mp0.getD k (Option.some huge) = Option.some k := by
          simp only [mp0]
          rw [List.getD_append _ _ _ _ (by simp; exact hk)]
          simp [hk]
        rw [hmk]
        refine ⟨(fun hm => by cases hm), (fun w hm => by cases hm; exact List.getD_append _ _ _ _ (by simp; exact hk))⟩
      · by_cases heq : k = 26
        · subst heq
          have hmk : mp0.getD 26 (Option.some huge) = Option.none := by
            simp only [mp0]
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [hmk]
          refine ⟨fun _ => ?_, fun _ hm => (by cases hm)⟩
          simp only [stepW]
          rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
          rw [hg0op, hg0in, List.map_nil, eval_and]
          rfl
        · have hmk : mp0.getD k (Option.some huge) = Option.some huge := by
            apply List.getD_eq_default
            simp [mp0]; omega
          rw [hmk]
          simp only [List.foldl_nil]
          refine ⟨(fun hm => by cases hm), fun w hm => ?_⟩
          cases hm
          rw [List.getD_eq_default _ _ (by simp [stepW]; omega), List.getD_eq_default _ _ (by simp [huge]; omega)]
    have h0 := go_prop gs [] mp0 hmono (by intro g hg; cases hg) (by simp) hmp0 (fun _ => false) (stepW (List.ofFn fun _ : Fin 26 => false) g0) (by simp [stepW, mp0]) (hinv0 (fun _ => false))
    have hres_out : ∃ out' : ℕ, res.2.getD out (Option.some huge) = Option.some out' := by
      cases ho : res.2.getD out (Option.some huge) with
      | some w => exact ⟨w, rfl⟩
      | none =>
        exfalso
        have hf := (h0.2.2 out).1 ho
        have hfalse : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn fun _ : Fin 26 => false) = true := by
          change (gs.foldl stepW (stepW (List.ofFn fun _ : Fin 26 => false) g0)).getD out false = true
          exact hf
        rw [hzero] at hfalse
        cases hfalse
    obtain ⟨out', hout'⟩ := hres_out
    refine ⟨⟨res.1, out'⟩, ?_, ?_, ?_⟩
    · exact h0.1
    · change res.1.length ≤ gs.length
      simpa using h0.2.1
    · intro x
      have hx := go_prop gs [] mp0 hmono (by intro g hg; cases hg) (by simp) hmp0 x (stepW (List.ofFn x) g0) (by simp [stepW, mp0]) (hinv0 x)
      have hxk := (hx.2.2 out).2 out' hout'
      change (res.1.foldl stepW (List.ofFn x)).getD out' false = (gs.foldl stepW (stepW (List.ofFn x) g0)).getD out false
      exact hxk.symm
  have perm_eval : ∀ (g0 : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (out : ℕ) (φ : Fin 26 → Fin 26) (swap0 : Bool)
      (hg0 : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g0.op = PEqualNP.CircuitLowerBounds.GateOp.or),
      let mapIn : ℕ → ℕ := fun i => if h : i < 26 then (φ ⟨i, h⟩).val else i
      let g0' : PEqualNP.CircuitLowerBounds.Gate :=
        if swap0 then ⟨g0.op, (g0.inputs.map mapIn).reverse⟩ else ⟨g0.op, g0.inputs.map mapIn⟩
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0' :: gs.map (fun g => ⟨g.op, g.inputs.map mapIn⟩), mapIn out⟩
      ∀ y : Fin 26 → Bool, C'.eval (List.ofFn y) = (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn (fun i => y (φ i))) := by
    intro g0 gs out φ swap0 hg0 mapIn g0' C' y
    have hsim : ∀ (rem : List PEqualNP.CircuitLowerBounds.Gate) (u v : List Bool),
        u.length = v.length →
        26 ≤ u.length →
        (∀ i, u.getD i false = v.getD (mapIn i) false) →
        ∀ k, (rem.foldl stepW u).getD k false = ((rem.map fun g => ⟨g.op, g.inputs.map mapIn⟩).foldl stepW v).getD (mapIn k) false := by
      intro rem
      induction rem with
      | nil =>
        intro u v _ _ hm k
        simpa using hm k
      | cons g rem ih =>
        intro u v hlen hu26 hm k
        simp only [List.map_cons, List.foldl_cons]
        have hbit : g.op.eval (g.inputs.map fun i => u.getD i false) =
            g.op.eval ((g.inputs.map mapIn).map fun i => v.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hm i
        let b := g.op.eval ((g.inputs.map mapIn).map fun i => v.getD i false)
        have hsu : stepW u g = u ++ [b] := by simp only [stepW, b]; rw [hbit]
        have hsv : stepW v ⟨g.op, g.inputs.map mapIn⟩ = v ++ [b] := rfl
        rw [hsu, hsv]
        apply ih (u ++ [b]) (v ++ [b]) (by simp; omega) (by simp; omega)
        intro m
        by_cases hm26 : m < 26
        · have hm26' : mapIn m < 26 := by simp [mapIn, hm26]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hm m
        · have hmap : mapIn m = m := by simp [mapIn, hm26]
          rw [hmap]
          rcases Nat.lt_trichotomy m u.length with hlt | heq | hgt
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
            simpa [hmap] using hm m
          · rw [heq, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, hlen,
                List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have h0 : g0'.op.eval (g0'.inputs.map fun i => (List.ofFn y).getD i false) =
        g0.op.eval (g0.inputs.map fun i => (List.ofFn (fun j => y (φ j))).getD i false) := by
      have hm0 : ∀ i, (List.ofFn (fun j => y (φ j))).getD i false = (List.ofFn y).getD (mapIn i) false := by
        intro i
        by_cases hi : i < 26
        · rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getD_eq_getElem _ _ (by simp [mapIn, hi])]
          rw [List.getElem_ofFn, List.getElem_ofFn]
          simp only [mapIn, dif_pos hi]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [mapIn, hi]; omega)]
      have hstraight : g0.op.eval ((g0.inputs.map mapIn).map fun i => (List.ofFn y).getD i false) =
          g0.op.eval (g0.inputs.map fun i => (List.ofFn (fun j => y (φ j))).getD i false) := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact (hm0 i).symm
      cases swap0 with
      | false =>
        change g0.op.eval ((g0.inputs.map mapIn).map fun i => (List.ofFn y).getD i false) = _
        exact hstraight
      | true =>
        change g0.op.eval (((g0.inputs.map mapIn).reverse).map fun i => (List.ofFn y).getD i false) = _
        rw [← hstraight, List.map_reverse]
        rcases hg0 with hop | hop <;> rw [hop]
        · rw [eval_and, eval_and]; simp
        · rw [eval_or, eval_or]; simp
    change ((g0' :: gs.map fun g => ⟨g.op, g.inputs.map mapIn⟩).foldl stepW (List.ofFn y)).getD (mapIn out) false =
      ((g0 :: gs).foldl stepW (List.ofFn fun i => y (φ i))).getD out false
    rw [List.foldl_cons, List.foldl_cons]
    symm
    apply hsim gs (stepW (List.ofFn fun i => y (φ i)) g0) (stepW (List.ofFn y) g0') (by simp [stepW]) (by simp [stepW])
    intro m
    by_cases hm26 : m < 26
    · have hm26' : mapIn m < 26 := by simp [mapIn, hm26]
      rw [List.getD_append _ _ _ _ (by simp; exact hm26), List.getD_append _ _ _ _ (by simp; exact hm26')]
      rw [List.getD_eq_getElem _ _ (by simp; exact hm26), List.getD_eq_getElem _ _ (by simp; exact hm26')]
      rw [List.getElem_ofFn, List.getElem_ofFn]
      simp only [mapIn, dif_pos hm26]
    · have hmap : mapIn m = m := by simp [mapIn, hm26]
      rw [hmap]
      by_cases heqm : m = 26
      · subst heqm
        simp only [stepW]
        rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
        exact h0.symm
      · rw [List.getD_eq_default _ _ (by simp [stepW]; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]
  have main : ∀ m (C : PEqualNP.CircuitLowerBounds.Circuit), C.size = m →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) →
      64 ≤ C.size := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro C hsize hMono hComp
      obtain ⟨gs_all, out⟩ := C
      cases gs_all with
      | nil =>
        let x1 : Fin 26 → Bool := fun i => decide (i.val = 0 ∨ i.val = 13)
        let x2 : Fin 26 → Bool := fun i => decide (i.val = 1 ∨ i.val = 15)
        have hx1 : (PEqualNP.CircuitLowerBounds.Circuit.mk [] out).eval (List.ofFn x1) = true :=
          (hComp x1).mpr ⟨0, 13, by decide +kernel, rfl, rfl⟩
        have hx2 : (PEqualNP.CircuitLowerBounds.Circuit.mk [] out).eval (List.ofFn x2) = true :=
          (hComp x2).mpr ⟨1, 15, by decide +kernel, rfl, rfl⟩
        change (List.ofFn x1).getD out false = true at hx1
        change (List.ofFn x2).getD out false = true at hx2
        by_cases hout : out < 26
        · rw [List.getD_eq_getElem _ _ (by simp; exact hout), List.getElem_ofFn] at hx1 hx2
          simp only [x1, x2, decide_eq_true_eq] at hx1 hx2
          omega
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hx1
          cases hx1
      | cons g0 gs =>
        have hg0 := hMono g0 (by simp)
        have hgs : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
          fun g hg => hMono g (by simp [hg])
        have shrink : ∀ (w : ℕ) (hw : w < 26 ∨ 26 + gs.length ≤ w)
            (heq : ∀ x : Fin 26 → Bool, g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (List.ofFn x).getD w false),
            64 ≤ (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).size := by
          intro w hw heq
          let mapW : ℕ → ℕ := fun k => if k < 26 then k else if k = 26 then w else k - 1
          let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs.map (fun g => ⟨g.op, g.inputs.map mapW⟩), mapW out⟩
          have hMono' : PEqualNP.MetaComplexity.Monotone2 C' := by
            intro g' hg'
            simp only [C', List.mem_map] at hg'
            rcases hg' with ⟨g, hg, rfl⟩
            have hgok := hgs g hg
            exact ⟨hgok.1, by simp [hgok.2]⟩
          have hComp' : ∀ x : Fin 26 → Bool, (C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) := by
            intro x
            rw [retarget_eval g0 gs out w hw heq x]
            exact hComp x
          have hlt : C'.size < m := by
            change C'.gates.length < m
            dsimp only [C']
            rw [List.length_map]
            change gs.length + 1 = m at hsize
            omega
          have h64 := ih C'.size hlt C' rfl hMono' hComp'
          change 64 ≤ C'.gates.length at h64
          dsimp only [C'] at h64
          rw [List.length_map] at h64
          change 64 ≤ gs.length + 1
          omega
        have hg0op : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g0.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
          simpa using hg0.1
        cases hin : g0.inputs with
        | nil =>
          rcases hg0op with hop | hop
          · have hzero : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn fun _ : Fin 26 => false) = false := by
              cases hev : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).eval (List.ofFn fun _ : Fin 26 => false) with
              | false => rfl
              | true =>
                exfalso
                obtain ⟨u, v, _, hu, _⟩ := (hComp (fun _ => false)).mp hev
                cases hu
            obtain ⟨C', hM', hsz', hev'⟩ := elimTrue_spec gs out g0 hop hin hgs hzero
            have hlt' : C'.size < m := by
              have hsz0 : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).size = gs.length + 1 := rfl
              omega
            have h64 := ih C'.size hlt' C' rfl hM' (fun x => by rw [hev' x]; exact hComp x)
            have hsz0 : (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).size = gs.length + 1 := rfl
            omega
          · exact shrink (26 + gs.length) (Or.inr (le_refl _)) (fun x => by
              rw [hop, hin, List.getD_eq_default _ _ (by simp)]
              rfl)
        | cons a rest =>
          cases hrest : rest with
          | nil =>
            have hin1 : g0.inputs = [a] := by rw [hin, hrest]
            by_cases ha : a < 26
            · exact shrink a (Or.inl ha) (fun x => by
                rw [hin1, List.map_cons, List.map_nil]
                rcases hg0op with hop | hop
                · rw [hop, eval_and]; simp
                · rw [hop, eval_or]; simp)
            · exact shrink (26 + gs.length) (Or.inr (le_refl _)) (fun x => by
                have hda : (List.ofFn x).getD a false = false := List.getD_eq_default _ _ (by simp; omega)
                have hdw : (List.ofFn x).getD (26 + gs.length) false = false := List.getD_eq_default _ _ (by simp)
                rw [hin1, List.map_cons, List.map_nil, hda, hdw]
                rcases hg0op with hop | hop
                · rw [hop, eval_and]; simp
                · rw [hop, eval_or]; simp)
          | cons b rest2 =>
            cases hrest2 : rest2 with
            | cons c rest3 =>
              exfalso
              have hlen2 := hg0.2
              rw [hin, hrest, hrest2] at hlen2
              simp at hlen2
            | nil =>
              have hin2 : g0.inputs = [a, b] := by rw [hin, hrest, hrest2]
              by_cases ha : a < 26
              · by_cases hb : b < 26
                · by_cases hab : a = b
                  · subst hab
                    exact shrink a (Or.inl ha) (fun x => by
                      rw [hin2, List.map_cons, List.map_cons, List.map_nil]
                      rcases hg0op with hop | hop
                      · rw [hop, eval_and]; simp
                      · rw [hop, eval_or]; simp)
                  · obtain ⟨φ, ψ, h1, h2, hrel, hcase⟩ := symm_pair ⟨a, ha⟩ ⟨b, hb⟩ (fun e => hab (congrArg Fin.val e))
                    have run_symm : ∀ (swap0 : Bool) (hres : (if swap0 then ([(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]).reverse else [(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]) = [0, 13] ∨
                        (if swap0 then ([(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]).reverse else [(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]) = [0, 15] ∨
                        (if swap0 then ([(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]).reverse else [(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val]) = [0, 1]),
                        64 ≤ (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).size := by
                      intro swap0 hres
                      let mapIn : ℕ → ℕ := fun i => if h : i < 26 then (φ ⟨i, h⟩).val else i
                      let g0' : PEqualNP.CircuitLowerBounds.Gate :=
                        if swap0 then ⟨g0.op, (g0.inputs.map mapIn).reverse⟩ else ⟨g0.op, g0.inputs.map mapIn⟩
                      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0' :: gs.map (fun g => ⟨g.op, g.inputs.map mapIn⟩), mapIn out⟩
                      have hMono' : PEqualNP.MetaComplexity.Monotone2 C' := by
                        intro g' hg'
                        simp only [C', List.mem_cons, List.mem_map] at hg'
                        rcases hg' with rfl | ⟨g, hg, rfl⟩
                        · cases swap0 <;> simp [g0', hg0.1, hin2]
                        · exact ⟨(hgs g hg).1, by simp [(hgs g hg).2]⟩
                      have hComp' : ∀ y : Fin 26 → Bool, (C'.eval (List.ofFn y) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ y u = true ∧ y v = true) := by
                        intro y
                        rw [perm_eval g0 gs out φ swap0 hg0op y, hComp (fun i => y (φ i))]
                        rw [computes_iff (fun i => y (φ i)), computes_iff y]
                        constructor
                        · rintro ⟨u, v, hr, hu, hv⟩
                          exact ⟨φ u, φ v, by rwa [hrel], hu, hv⟩
                        · rintro ⟨u, v, hr, hu, hv⟩
                          refine ⟨ψ u, ψ v, ?_, by simpa [h2] using hu, by simpa [h2] using hv⟩
                          rw [← hrel (ψ u) (ψ v), h2, h2]
                          exact hr
                      have hex : g0'.inputs = [0, 13] ∨ g0'.inputs = [0, 15] ∨ g0'.inputs = [0, 1] := by
                        have hmap_in : g0.inputs.map mapIn = [(φ ⟨a, ha⟩).val, (φ ⟨b, hb⟩).val] := by simp [hin2, mapIn, ha, hb]
                        cases swap0 <;> simpa [g0', hmap_in] using hres
                      have hsz : C'.size = (PEqualNP.CircuitLowerBounds.Circuit.mk (g0 :: gs) out).size := by
                        change (g0' :: gs.map fun g => ⟨g.op, g.inputs.map mapIn⟩).length = (g0 :: gs).length
                        simp
                      rw [← hsz]
                      have hComp_compact : ∀ y : Fin 26 → Bool, (C'.eval (List.ofFn y) = true ↔ ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val - 13) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ y u = true ∧ y v = true) := by
                        intro y
                        rw [hComp' y]
                        constructor
                        · rintro ⟨u, v, huv, hu, hv⟩; have h := (edges_compact u v).mp huv; exact ⟨u, v, h.1, h.2.1, h.2.2, hu, hv⟩
                        · rintro ⟨u, v, h1, h2, h3, hu, hv⟩; exact ⟨u, v, (edges_compact u v).mpr ⟨h1, h2, h3⟩, hu, hv⟩
                      rcases hex with h013 | h015 | h01
                      · exact h_edge C' hMono' ⟨g0', rfl, h013⟩ hComp_compact
                      · exact h_noninc C' hMono' ⟨g0', rfl, h015⟩ hComp_compact
                      · exact h_pts C' hMono' ⟨g0', rfl, h01⟩ hComp_compact
                    rcases hcase with ⟨ha0, hb1 | hb13 | hb15⟩ | ⟨hb0, ha1 | ha13 | ha15⟩
                    · exact run_symm false (by simp [ha0, hb1])
                    · exact run_symm false (by simp [ha0, hb13])
                    · exact run_symm false (by simp [ha0, hb15])
                    · exact run_symm true (by simp [hb0, ha1])
                    · exact run_symm true (by simp [hb0, ha13])
                    · exact run_symm true (by simp [hb0, ha15])
                · rcases hg0op with hop | hop
                  · exact shrink (26 + gs.length) (Or.inr (le_refl _)) (fun x => by
                      have hdb : (List.ofFn x).getD b false = false := List.getD_eq_default _ _ (by simp; omega)
                      have hdw : (List.ofFn x).getD (26 + gs.length) false = false := List.getD_eq_default _ _ (by simp)
                      rw [hop, hin2, List.map_cons, List.map_cons, List.map_nil, hdb, hdw, eval_and]
                      simp)
                  · exact shrink a (Or.inl ha) (fun x => by
                      have hdb : (List.ofFn x).getD b false = false := List.getD_eq_default _ _ (by simp; omega)
                      rw [hop, hin2, List.map_cons, List.map_cons, List.map_nil, hdb, eval_or]
                      simp)
              · by_cases hb : b < 26
                · rcases hg0op with hop | hop
                  · exact shrink (26 + gs.length) (Or.inr (le_refl _)) (fun x => by
                      have hda : (List.ofFn x).getD a false = false := List.getD_eq_default _ _ (by simp; omega)
                      have hdw : (List.ofFn x).getD (26 + gs.length) false = false := List.getD_eq_default _ _ (by simp)
                      rw [hop, hin2, List.map_cons, List.map_cons, List.map_nil, hda, hdw, eval_and]
                      simp)
                  · exact shrink b (Or.inl hb) (fun x => by
                      have hda : (List.ofFn x).getD a false = false := List.getD_eq_default _ _ (by simp; omega)
                      rw [hop, hin2, List.map_cons, List.map_cons, List.map_nil, hda, eval_or]
                      simp)
                · exact shrink (26 + gs.length) (Or.inr (le_refl _)) (fun x => by
                    have hda : (List.ofFn x).getD a false = false := List.getD_eq_default _ _ (by simp; omega)
                    have hdb : (List.ofFn x).getD b false = false := List.getD_eq_default _ _ (by simp; omega)
                    have hdw : (List.ofFn x).getD (26 + gs.length) false = false := List.getD_eq_default _ _ (by simp)
                    rw [hin2, List.map_cons, List.map_cons, List.map_nil, hda, hdb, hdw]
                    rcases hg0op with hop | hop
                    · rw [hop, eval_and]; simp
                    · rw [hop, eval_or]; simp)
  intro C hMono hComp
  exact main C.size C rfl hMono hComp
