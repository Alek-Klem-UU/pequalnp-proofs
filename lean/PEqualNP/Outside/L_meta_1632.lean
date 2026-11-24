import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

theorem raw_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun j => s.getD j false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem raw (N : Nat) (gs : List Gate) (p : Fin N) (x : Fin N → Bool) :
    (Circuit.mk gs p.val).eval (List.ofFn x) = x p := by
  unfold Circuit.eval Circuit.wires
  rw [raw_fold _ _ _ (by simpa using p.isLt)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, p.isLt, ↓reduceDIte, Option.getD_some]

end PEqualNP.Outside.L_meta_1632


theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ hinter _ _ _ _
  have disjointOff {l m a b : Fin N} (hlm : l ≠ m)
      (ha : a ∈ L l) (ham : a ∈ L m) (hb : b ∈ L l) (hba : b ≠ a) : b ∉ L m := by
    intro hbm
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hinter l m hlm)
    have h1 := Finset.mem_inter.mpr ⟨ha, ham⟩
    have h2 := Finset.mem_inter.mpr ⟨hb, hbm⟩
    rw [hc, Finset.mem_singleton] at h1 h2
    exact hba (h2.trans h1.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l m hl hm hlm b hb hba
    exact ⟨hm.2, disjointOff hlm hl.1 hm.1 hb hba⟩
  · intro l m hl hm hlm b hb hba
    exact ⟨hm.2, disjointOff hlm hl.1 hm.1 hb hba⟩
  · exact fun _ h => h.2
  · exact fun _ h => h.2
  · exact fun _ _ _ hm _ _ hb => ⟨hm.2, hb⟩
  · intro l m hl hm
    exact Finset.card_eq_one.mp (hinter l m (fun e => hm.2 (e ▸ hl.1)))
  · intro gates _ _ _ p t
    rw [PEqualNP.Outside.L_meta_1632.raw N gates p (fun v : Fin N => decide (v ∉ L t))]
    simp
