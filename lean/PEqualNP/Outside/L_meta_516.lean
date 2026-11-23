import Mathlib
import PEqualNP.Defs

-- The generic circuit and six-row bounds are adapted from the checked proof of L-meta-550.

namespace Theta516
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

end Theta516

namespace Theta516
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

end Theta516

namespace Theta516

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

end Theta516

namespace Theta516
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl



def rows516 : List Nat := [0, 1, 3, 4, 6, 9, 20, 33, 36, 1, 3, 4, 6, 9, 22, 0, 4, 6, 20, 24, 1, 4, 8, 9, 0, 1, 3, 20, 22, 1, 9, 16, 24, 41, 88, 137, 152, 0, 8, 9, 20, 22, 24, 88, 148, 152, 0, 22, 0, 0, 0, 0, 84, 86, 88, 82, 88, 0, 84, 88, 0, 86, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 4, 6, 9, 68, 129, 132, 1, 3, 4, 6, 9, 70, 0, 4, 6, 68, 72, 1, 4, 8, 9, 0, 1, 3, 68, 70, 1, 9, 64, 72, 137, 88, 41, 104, 0, 8, 9, 68, 70, 72, 88, 100, 104, 0, 70, 0, 0, 0, 0, 84, 86, 88, 82, 88, 0, 84, 88, 0, 86, 0, 148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 16, 18, 33, 20, 9, 24, 1, 3, 16, 18, 33, 22, 0, 16, 18, 20, 36, 1, 16, 32, 33, 0, 1, 3, 20, 22, 1, 33, 4, 36, 41, 100, 161, 164, 0, 32, 33, 20, 22, 36, 100, 148, 164, 0, 22, 0, 0, 0, 0, 84, 86, 100, 70, 100, 0, 84, 100, 0, 86, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 16, 18, 33, 80, 129, 144, 1, 3, 16, 18, 33, 82, 0, 16, 18, 80, 96, 1, 16, 32, 33, 0, 1, 3, 80, 82, 1, 33, 64, 96, 161, 100, 41, 104, 0, 32, 33, 80, 82, 96, 100, 88, 104, 0, 82, 0, 0, 0, 0, 84, 86, 100, 70, 100, 0, 84, 100, 0, 86, 0, 148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 64, 66, 129, 68, 9, 72, 1, 3, 64, 66, 129, 70, 0, 64, 66, 68, 132, 1, 64, 128, 129, 0, 1, 3, 68, 70, 1, 129, 4, 132, 137, 148, 161, 164, 0, 128, 129, 68, 70, 132, 148, 100, 164, 0, 70, 0, 0, 0, 0, 84, 86, 148, 22, 148, 0, 84, 148, 0, 86, 0, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 64, 66, 129, 80, 33, 96, 1, 3, 64, 66, 129, 82, 0, 64, 66, 80, 144, 1, 64, 128, 129, 0, 1, 3, 80, 82, 1, 129, 16, 144, 161, 148, 137, 152, 0, 128, 129, 80, 82, 144, 148, 88, 152, 0, 82, 0, 0, 0, 0, 84, 86, 148, 22, 148, 0, 84, 148, 0, 86, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 8, 9, 6, 40, 18, 24, 2, 3, 8, 9, 6, 41, 0, 8, 9, 40, 36, 2, 8, 4, 6, 0, 2, 3, 40, 41, 2, 6, 32, 36, 22, 164, 70, 100, 0, 4, 6, 40, 41, 36, 164, 104, 100, 0, 41, 0, 0, 0, 0, 168, 169, 164, 161, 164, 0, 168, 164, 0, 169, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 8, 9, 6, 136, 66, 72, 2, 3, 8, 9, 6, 137, 0, 8, 9, 136, 132, 2, 8, 4, 6, 0, 2, 3, 136, 137, 2, 6, 128, 132, 70, 164, 22, 148, 0, 4, 6, 136, 137, 132, 164, 152, 148, 0, 137, 0, 0, 0, 0, 168, 169, 164, 161, 164, 0, 168, 164, 0, 169, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 32, 33, 18, 40, 6, 36, 2, 3, 32, 33, 18, 41, 0, 32, 33, 40, 24, 2, 32, 16, 18, 0, 2, 3, 40, 41, 2, 18, 8, 24, 22, 152, 82, 88, 0, 16, 18, 40, 41, 24, 152, 104, 88, 0, 41, 0, 0, 0, 0, 168, 169, 152, 137, 152, 0, 168, 152, 0, 169, 0, 164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 32, 33, 18, 160, 66, 96, 2, 3, 32, 33, 18, 161, 0, 32, 33, 160, 144, 2, 32, 16, 18, 0, 2, 3, 160, 161, 2, 18, 128, 144, 82, 152, 22, 148, 0, 16, 18, 160, 161, 144, 152, 164, 148, 0, 161, 0, 0, 0, 0, 168, 169, 152, 137, 152, 0, 168, 152, 0, 169, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 128, 129, 66, 136, 6, 132, 2, 3, 128, 129, 66, 137, 0, 128, 129, 136, 72, 2, 128, 64, 66, 0, 2, 3, 136, 137, 2, 66, 8, 72, 70, 104, 82, 88, 0, 64, 66, 136, 137, 72, 104, 152, 88, 0, 137, 0, 0, 0, 0, 168, 169, 104, 41, 104, 0, 168, 104, 0, 169, 0, 164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 128, 129, 66, 160, 18, 144, 2, 3, 128, 129, 66, 161, 0, 128, 129, 160, 96, 2, 128, 64, 66, 0, 2, 3, 160, 161, 2, 66, 32, 96, 82, 104, 70, 100, 0, 64, 66, 160, 161, 96, 104, 164, 100, 0, 161, 0, 0, 0, 0, 168, 169, 104, 41, 104, 0, 168, 104, 0, 169, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 12, 12, 12, 12, 12, 13, 13, 13, 13, 15, 21, 21, 21, 23, 25, 25, 25, 25, 25, 25, 25, 25, 27, 28, 28, 28, 28, 28, 28, 28, 28, 29, 30, 31, 60, 61, 63, 85, 87, 89, 90, 90, 91, 92, 92, 93, 94, 95, 108, 109, 111, 124, 125, 126, 127, 252, 253, 255, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 12, 12, 12, 12, 12, 13, 13, 13, 13, 15, 69, 69, 69, 71, 73, 73, 73, 73, 73, 73, 73, 73, 75, 76, 76, 76, 76, 76, 76, 76, 76, 77, 78, 79, 204, 205, 207, 85, 87, 89, 90, 90, 91, 92, 92, 93, 94, 95, 156, 157, 159, 220, 221, 222, 223, 252, 253, 255, 17, 17, 17, 17, 17, 17, 17, 17, 17, 19, 19, 19, 19, 19, 19, 48, 48, 48, 48, 48, 49, 49, 49, 49, 51, 21, 21, 21, 23, 37, 37, 37, 37, 37, 37, 37, 37, 39, 52, 52, 52, 52, 52, 52, 52, 52, 53, 54, 55, 60, 61, 63, 85, 87, 101, 102, 102, 103, 116, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 252, 253, 255, 17, 17, 17, 17, 17, 17, 17, 17, 17, 19, 19, 19, 19, 19, 19, 48, 48, 48, 48, 48, 49, 49, 49, 49, 51, 81, 81, 81, 83, 97, 97, 97, 97, 97, 97, 97, 97, 99, 112, 112, 112, 112, 112, 112, 112, 112, 113, 114, 115, 240, 241, 243, 85, 87, 101, 102, 102, 103, 116, 116, 117, 118, 119, 180, 181, 183, 244, 245, 246, 247, 252, 253, 255, 65, 65, 65, 65, 65, 65, 65, 65, 65, 67, 67, 67, 67, 67, 67, 192, 192, 192, 192, 192, 193, 193, 193, 193, 195, 69, 69, 69, 71, 133, 133, 133, 133, 133, 133, 133, 133, 135, 196, 196, 196, 196, 196, 196, 196, 196, 197, 198, 199, 204, 205, 207, 85, 87, 149, 150, 150, 151, 212, 212, 213, 214, 215, 216, 217, 219, 220, 221, 222, 223, 252, 253, 255, 65, 65, 65, 65, 65, 65, 65, 65, 65, 67, 67, 67, 67, 67, 67, 192, 192, 192, 192, 192, 193, 193, 193, 193, 195, 81, 81, 81, 83, 145, 145, 145, 145, 145, 145, 145, 145, 147, 208, 208, 208, 208, 208, 208, 208, 208, 209, 210, 211, 240, 241, 243, 85, 87, 149, 150, 150, 151, 212, 212, 213, 214, 215, 228, 229, 231, 244, 245, 246, 247, 252, 253, 255, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 14, 14, 14, 14, 15, 42, 42, 42, 43, 38, 38, 38, 38, 38, 38, 38, 38, 39, 44, 44, 44, 44, 44, 44, 44, 44, 46, 45, 47, 60, 62, 63, 170, 171, 166, 165, 165, 167, 172, 172, 174, 173, 175, 156, 158, 159, 188, 190, 189, 191, 252, 254, 255, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 14, 14, 14, 14, 15, 138, 138, 138, 139, 134, 134, 134, 134, 134, 134, 134, 134, 135, 140, 140, 140, 140, 140, 140, 140, 140, 142, 141, 143, 204, 206, 207, 170, 171, 166, 165, 165, 167, 172, 172, 174, 173, 175, 108, 110, 111, 236, 238, 237, 239, 252, 254, 255, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 48, 48, 48, 48, 48, 50, 50, 50, 50, 51, 42, 42, 42, 43, 26, 26, 26, 26, 26, 26, 26, 26, 27, 56, 56, 56, 56, 56, 56, 56, 56, 58, 57, 59, 60, 62, 63, 170, 171, 154, 153, 153, 155, 184, 184, 186, 185, 187, 180, 182, 183, 188, 190, 189, 191, 252, 254, 255, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 35, 35, 35, 35, 48, 48, 48, 48, 48, 50, 50, 50, 50, 51, 162, 162, 162, 163, 146, 146, 146, 146, 146, 146, 146, 146, 147, 176, 176, 176, 176, 176, 176, 176, 176, 178, 177, 179, 240, 242, 243, 170, 171, 154, 153, 153, 155, 184, 184, 186, 185, 187, 120, 122, 123, 248, 250, 249, 251, 252, 254, 255, 130, 130, 130, 130, 130, 130, 130, 130, 130, 131, 131, 131, 131, 131, 131, 192, 192, 192, 192, 192, 194, 194, 194, 194, 195, 138, 138, 138, 139, 74, 74, 74, 74, 74, 74, 74, 74, 75, 200, 200, 200, 200, 200, 200, 200, 200, 202, 201, 203, 204, 206, 207, 170, 171, 106, 105, 105, 107, 232, 232, 234, 233, 235, 228, 230, 231, 236, 238, 237, 239, 252, 254, 255, 130, 130, 130, 130, 130, 130, 130, 130, 130, 131, 131, 131, 131, 131, 131, 192, 192, 192, 192, 192, 194, 194, 194, 194, 195, 162, 162, 162, 163, 98, 98, 98, 98, 98, 98, 98, 98, 99, 224, 224, 224, 224, 224, 224, 224, 224, 226, 225, 227, 240, 242, 243, 170, 171, 106, 105, 105, 107, 232, 232, 234, 233, 235, 216, 218, 219, 248, 250, 249, 251, 252, 254, 255]

def xs516 : List Nat := [0x9931d4c01008803f004c98ea600804401f80264c75300402200fc013263a9802011007e009931d4c01008803f004c98ea600804401f80356a4fa807fffe0ffffab527d403ffff07fffd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffab527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6, 0xd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffab527d403ffff07fffd5a93ea01ffff83fffead49f500ffffc1fffe64c75300402200fc013263a9802011007e009931d4c01008803f004c98ea600804401f80264c75300402200fc013263a9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414, 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffe0000000000001fc7ffffffffe000000fffff80000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958, 0xfffff80000000000007f1fffffffff8000003ffffe0000000000001fc7ffffffffe000000fffe1fffe00fffffffffff0ffff007fffffff800000000000000001ff800e000000000000e000000000000000007fe0038000000000003ffff9fffffc3ff0001ffffcfffffe1ff80000056f8040200000000000b7c2fc5660310100015be0100800000000002df0bf15980c404000521849800c13acac00290c24c00609d6560000000603000000000008000000200000180000000180c00000000002000000080000060000128059be819040400009402cdf40c82020, 0xffc0070000000000007000000000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000e000000000000000007fe0038000000000003f8fffffffffc000001fffff0000000000000fffe1fffe00fffffffffff0ffff007fffffffffffe0000000000001fc7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040, 0xfe3fffffffff0000007ffffc0000000000003fff87fff803ffffffffffc3fffc01ffffffffffff80000000000007f1fffffffff8000003ff001c000000000001c00000000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003800000000000000001ff800e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180, 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001c00000000000000000ffc0070000000000007000000000000000003fff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007ffffc0000000000003f8fffffffffc000001fffff00000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000, 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff0000000000000fe3fffffffff0000007ffffc0000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007000000000000000003ff001c000000000001c0000000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000]

abbrev f516 : BFn 8 := (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem enc_inputs516 :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rows516)
      = xs516 := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem enc_goal516 : encL f516 rows516 = goal 876 := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem mask516 : mask 876 = 2 ^ rows516.length - 1 := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem proper_fail516 : ∀ zs ∈ xs516.sublists, zs ≠ xs516 →
    (cov 876 zs &&& lo 876) ≠ lo 876 := by decide +kernel

theorem no_sub516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 876) (goal 876) s xs516) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xs516 → NatRun (mask 876) (goal 876) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs516
  · subst e; exact noRunFull s hs h
  · exact proper_fail516 zs (List.mem_sublists.2 hz) e (required h)

theorem main516 (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 876) (goal 876) s xs516) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f516 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 876) (encL f516 rows516) s' (ws.map fun a => encL a rows516) :=
    Run.map (fun a : BFn 8 => encL a rows516)
      (fun a => by rw [mask516]; exact encL_inv a rows516)
      (fun a b => encL_and a b rows516) (fun a b => encL_or a b rows516) hrun
  rw [enc_goal516] at hr
  refine no_sub516 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs516]
  exact hsub.map _

end Theta516


namespace Theta516

def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h

end Theta516

namespace Theta516

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end Theta516

namespace Theta516

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 2047
    let b := (code >>> 11) &&& 2047
    let c := (code >>> 22) &&& 2047
    let d := (code >>> 33) &&& 2047
    let e := (code >>> 44) &&& 2047
    let f := (code >>> 55) &&& 2047
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end Theta516

namespace Theta516

def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end Theta516

namespace Theta516

def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/32 < N s && (rot (v/2 % 16) zs).isPerm (S s (v/32)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/32 < N s && (rot (v/2 % 16) zs).isPerm (S s (v/32))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end Theta516



namespace Theta516

def w0 : Nat := 0x0

def w1 : Nat := 0xe00000000000001c000000000ffc000000003fffff87fe000000006000000000000000003000001e000000003ff80000000000000f1fffffffff800000000f863ff803ffffffe3ffc3fffc01fffffff000000100c0000000000000000008000002000000000010000000000000000002000001800000000065206010100000000936d032080800149600000000000000024b09300980440400016f8040200000000000b7c23c16603101000048612600304eb0b000a430830018275958

def w2 : Nat := 0x3f800e00000000000001ffe0fffff0ffc0000ffff3fffff87fe00000007e00000000000000003f0003ffe00000001fff80000000000000f1fffffffff800000007f863ff803ffffffe3ffc3fffc01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w3 : Nat := 0x3fffffe00000fffffffffffff000000000000ffffff800003ffffffffffffc000000000000000000000000000000000000000000000000ffffff800003ffffffffffffc000000000003fffffe00000fffffffffffffffa947a01053884343ffd4a3d00829c421a1ffea41e81d0cfe77c7fff520fc7e3ffffffffffa907a07433f9df1fffd483f1f8ffffffffffea51e80414e210d0fff528f4020a7108687ffa907a07433f9df1fffd483f1f8ffffffffffea41e81d0cfe77c7fff520fc7e3ffffffff

def w4 : Nat := 0xff80000000000000000000000000000000003fe0000000000000000000ffffff8000000000007fffffc00006000003c00fffe00003000001e007fff00001800000f003fff80000c000007801fffc00ffe3fffffffffffe007ff1ffffffffffffffa907a07533e85353ffd483d93ef9f629a9ffea41e81d4cfa14d4fff520f64fbe7d8a6a7ffa907a07533f9dfdfffd483d03a99fcefefffeed7fa6417e6fbcbffff6bfc320bf37dfdfffbb5fe9905f9bef2ffffdaff0c82fcdf7f7ffeffff9fcbfffffcffff7fffcfe5fffffe7f

def w5 : Nat := 0x7ffffffffffff80e0000000007fffffc00001ffffffffffffe038000000001ffffff0001e0001ff00000000000f0000ff800000007ffffffffffffffffe007ff1ffffffffffff1fffffffffffffffff801ffc7fffffffffffc00006000003c00fffe00003000001e007fffffa907fbfdfffffffffff483d03a99fcefefffea41feff7ffffffffffd20f40ea67f3bfbfffade7b67ff3ec5353ffd6f3db3ff9f629a9fffffff9fcfffffffffff7ffffffdfffffe7fffffffe7f3ffffffffffdfffffff7fffff9ffffed7fa6417e6fbfbffff6bfd320bf37dfdf

def w6 : Nat := 0x1800000f003fff80000c000007801fffc00ffe3fffffffffffe3fffffffffffffffff003ff8ffffffffffff8fffffffffffffffffc000780007fc00000000003c0003fe000000001c000000000ffffff800003ffffffffffffc070000000003fffffe00000ffffffffffffffffb5fe9905f9befeffffdaff4c82fcdf7f7ffefffffffbfffffcffffffffcfe7ffffffffffbffffffeffffff3ffffffff3f9ffffffffffeb79ed9ffcfb14d4fff5bcf6cffe7d8a6a7ffe907a07533f9dfdfffd483fdfefffffffffffa41e81d4cfe77f7fff520ff7fbffffffff

def w7 : Nat := 0x20000ff00000000000100007f80000000030000000001ff03fe0000067fdfeeff81ff00c0000000007fc0ff8000019ff7fbbfe07fc0000000000000000000000000000000000000016c05fe00007c000052b60aff00003e0000005b017f80001f000014ad82bfc0000f8000ffada7b67ff1ec5151ffd6d3db3ff8f628a8fffa41e81d4c7e35757ff520f75fbebfdabebffe907a07531f8d5d5ffd483dd7efaff6afafffed7fa641324fb2b3fff6bfd3209927d959ffbfffffbaccb7ec2cfffffff3d9665bf6567fefffffeeb32dfb0b3ffffffcf65996fd959

def w8 : Nat := 0x20000ff00000000000100007f80000000030000000003fffffe00000fffffffffffff00c000000000ffffff800003ffffffffffffc0000000000000000000000000000000000000016c05fe000ffffff852b63ffffffffffffc005b017f8003fffffe14ad8fffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w9 : Nat := 0x20000ff0000000000010000ff80000000030000000001ff03fe0000067fffeeff81ff00c000000000ffffff8000019ff7fbffffffc00006000003c00fffe00003000001e007fff0016d85fe00f07ffff852b6caff00783ffffc00ffe3fffffffffffe14fff3ffffffffffffffada7b67ff3ec5353ffd6d3db3ff9f629a9fffa41e81d4cfe35f5fff520f75fbeffdafefffe907a07533f9dfdfffd483dd7efbffeffffffed7fa6417e6fbebffff6bfd320bf37dfdfffbfffffbadfbfef2ffffffff3d96fdff7f7ffeffffffebfffffcffffffffcfe5ffffff7f

def w10 : Nat := 0xc000000000000000006000000000000000100000000001f0000000002bfc0000f800000400000000007c000000000aff00003e000000002000001c0003fe00001000000e0001ff000e283feff77fc0ff8367159ff7fbbfe07fc0038a0ffbfddff03fe0d9c567fdfeeff81ffffade7b63ac0a44000ffd6f3db1d605220007ffa41e80c002c73233ff520ff771996fd959ffe907a03000b1cc8cffd483fddc665bf6567ffac3ea241566b1797ffd61f5120ab358bcbffafafbefef5fed535fff7d7d379faff6afaffebebefbfbd7fb54d7ffdf5f4de7ebfdabeb

def w11 : Nat := 0xc00000000000000000600000000000000015b017f80001f000014ad82bfc0000f80000056c05fe00007c000052b60aff00003e00000000a0003fdc0003fe000050001fee0001ff00ce283feff77fc0ff8367159ff7fbbfe07fc0338a0ffbfddff03fe0d9c567fdfeeff81ffffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567ffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabeb

def w12 : Nat := 0xc0000000000000000060000ff800000000100000000001f0000000002bfffe00f8000004000000000ffffff800000aff0007fffffc00006000003c00fffe00003000001e007fff000e383fefff7fffff83671d9ff7ffbfffffc00ffe3fffffffffffe0dfff7ffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w13 : Nat := 0x120001ff0000000000090000ff80000000060000000003e0fffe00000d403ffff07fff018000000000f83fff800003500ffffc1fffc00004000002000fc00000020000010007e000031d0c01008803f000c98ea600804401f80000c74300402200fc003263a9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w14 : Nat := 0x1c00010000000000000e0000800000000004000000000200fc00000009802011007e00010000000000803f00000002600804401f80000006000003c00fffe00003000001e007fff002938a01ffff83fff8ad49f500ffffc1fffc00a4e2807fffe0fffe2b527d403ffff07fff0000400000020002020000200000010001010000000000008042828000000820014025414000000000002010a0a000000208005009505000000000004c200d0c000000000026100686000000004433481313000000002099a409a980000000110cd204c4c0000000082669026a6

def w15 : Nat := 0x1d0001008003f000000e8000804001f80004c74300402200fc003263a9802011007e000131d0c01008803f000c98ea600804401f8000004e0007ffc00fffe000270003ffe007fff01a938a01ffff83fff8ad49f500ffffc1fffc06a4e2807fffe0fffe2b527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w16 : Nat := 0x1e00000000000000000f0000ff8000000007000000000000000000000ffffffe00000001c000000000ffffff800003fff007ffffffc0000000000000000000000000000000000000000000000000000000fe003800000000000000ff83ffffc3ff00003fffcfffffe1ff80000004e00402000000000002700b05600200000010000000000000000000000b711980c4040004000000000118c8c00000024c00609d6560000000200000000000008000000000000180000000180c00000000002000000080000060000128059ba819040400009400cc740c82020

def w17 : Nat := 0x1e0001ff00000000000f0000ff8000000000000000000000fffe00000000001e007fff01c000000000ffffff8000007fffffffffffc00000000000000fffe00000000001e007fff0001e0001ff00000000000f0000ff80000000000003fffffffffffe038000000001ffffffffade7b67ef3ec5313ffd6f3d339f9f629a9fffa41e80404e673f3fff520fd320bf37dfdfffe907a07133f9dfdfffd483fdfe7fffff9ffffa41e80404e673f3fff520fd320bf37dfdfffade7b67ef3ec5313ffd6f3d339f9f629a9ffea41feff3fffffcffffd20f40e267f3bfbf

def w18 : Nat := 0x1e0001ff00000000000f0000ff8000000000000000000000fffe000000003ffe007fff01c000000000ffffff8000007fffffffffffc00006000003c00fffe00003000001e007fff0001f8001fff003fff8000fc000fff801fffc00ffe3fffffffffffe03fff1ffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w19 : Nat := 0x1e0001ff00000000000f0000ff80000000030000000001fffffe0000067fdffeffffff01c000000000ffffff800001ffffffffffffc00000000000000fffe00000000001e007fff0017e05ffff007c000052bf0affff803e0000005b03fffffffffffe17ad82bfc001ffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w20 : Nat := 0x1e0001ff00000000000f0000ff8000000007000000000000000000000000000000000001c000000000000000000000000000000000000006000003c00fffe00003000001e007fff003ff8ffffff0000000ffffc000000000000000ffe3fffffc0000003ffff00000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w21 : Nat := 0x1e0001ff00000000000f0000ff80000000070000000003e0fffe00000d403ffff07fff01c000000000f83fff800003500ffffc1fffc00006000003c00fffe00003000001e007fff003ff8ffffff803f000ffffe600804401f80000ffe3fffffe00fc003ffff9802011007e000004a0166fb36c13530002500b37d9b609a980100000114cd204f4c000000309a669026a60040000045334813d30000000c2699a409a980149612600384ebab800a4b093001c275d5c0016f85f8ace072a2a002b7c2281050095050005be17e2b381ca8a800adf08a0414025414

def w22 : Nat := 0x1e0001ff00000000000f0000ff80000000070000000003fffffe00000fffffffffffff01c000000000ffffff800003ffffffffffffc00006000003c00fffe00003000001e007fff003ff8ffffffffffff8fffffffffffffffffc00ffe3fffffffffffe3fffffffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w23 : Nat := 0x1e0001ff00000000000f0000ff80000000075b017f8003fffffe14ad8fffffffffffff01d6c05fe000ffffff852b63ffffffffffffc0000e0003ffc00fffe000070001ffe007fff00fff8ffffffffffff8fffffffffffffffffc03ffe3fffffffffffe3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def w24 : Nat := 0x1f8001fff003fff8000fc000fff801fffc07ffe3fffffffffffe3fffffffffffffffff01fff8ffffffffffff8fffffffffffffffffc0007e0007ffc00fffe0003f0003ffe007fff01fff8ffffffffffff8fffffffffffffffffc07ffe3fffffffffffe3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def w25 : Nat := 0x3ff8ffffffffffff8fffffffffffffffffc00006000003c00fffe00003000001e007fff1fffffffffffffffff801ffc7fffffffffffc070000000003fffffe00000fffffffffffff0001e0001ff00000000000f0000ff8000000000001ffffffffffffe038000000001ffffffffbffffffeffffff3ffffffff3f9fffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffffffe7f3ffffffffffdfffffff7fffff9ffffa41e81d4cfe77f7fff520ff7fbffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9ffea41feff7ffffffffffd20f40ea67f3bfbf

def w26 : Nat := 0x1c000000000ffffff800003ffffffffffffc000780007fc00000000003c0003fe0000000000007ffffffffffff80e0000000007fffffc00ffe3fffffffffffe3fffffffffffffffff00001800000f003fff80000c000007801fffc7ffffffffffffffffe007ff1ffffffffffffffe907a07533f9dfdfffd483fdfeffffffffffeb79ed9ffcfb14d4fff5bcf6cffe7d8a6a7ffa907fbfdfffffffffff483d03a99fcefefffefffffffbfffffcffffffffcfe7fffffffffffb5fe9905f9befeffffdaff4c82fcdf7f7fffffff9fcfffffffffff7ffffffdfffffe7f

def w27 : Nat := 0x1c01800000fffffff80000fffffffffffffc00ffe3fffffffffffe3fffffffffffffffff003fffffffffffffff8fffffffffffffffffc00ffe3fffffffffffe3fffffffffffffffff01c01800000fffffff80000fffffffffffffc7ffffffffffffffffe007ffffffffffffffffffb5fe9f57ffbfffffffdaffdfeffffffffffefffffffffffffdffffffffefffffffffffffbffffffffffffffffffffff3fbffffffffffefffffffffffffdffffffffeffffffffffffffb5fe9f57ffbfffffffdaffdfefffffffffffffff9fdfffffffffff7fffffffffffffff

def w28 : Nat := 0x1c1e0001ff0ffffff8000f3ffffffffffffc070780007fc3fffffe0003cfffffffffffff01c007ffffffffffff80e003ffffffffffffc00ffe3fffffffffffe3fffffffffffffffff003ff8ffffffffffff8fffffffffffffffffc7ffffffffffffffffe3fffffffffffffffffffede7b67ff3fddfdfffd6f3fffffffffffffffb79ed9ffcff77f7fff5bcfffffffffffffffe907fbfdfffffffffff483fdfeffffffffffffffffffbffffffffffffffdfe7fffffffffffffffffefffffffffffffff7f9fffffffffffffffffffffffffffffffffffffffffffff

def w29 : Nat := 0x810c040000000000004086020000000000002043010000000000001021808000000000000810c040000000000004086020000000000011220a8803fdde003fe891054401feef001ff44882a200ff77800ffa244151007fbbc007fd1220a8803fdde003fe891054401feef001ff001050410008012808000828208004009404000414104002004a0200020a082001002501000105041000801280800082820800400940400000000114c5204544000000008a629022a2000000004531481151000000002298a408a880000000114c5204544000000008a629022a2

def w30 : Nat := 0x811c04010000000000408e0200800000000024430100000200fc00102189802011007e000910c0400000803f00040862600804401f8011220e8803ffde0fffe891074401ffef07fff44a93aa01ffff83fffaad49f500ffffc1fffd12a4ea807fffe0fffeab527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w31 : Nat := 0x1fffffffffffffffff801ffc7fffffffffffc7ffffffffffffffffe007ff1ffffffffffff00001800000f003fff80000c000007801fffc00001ffffffffffffe038000000001ffffff000007ffffffffffff80e0000000007fffffc000780007fc00000000003c0003fe0000000ffffffe7f3ffffffffffdfffffff7fffff9ffffffff9fcfffffffffff7ffffffdfffffe7ffffb5fe9905f9befeffffdaff4c82fcdf7f7ffea41feff7ffffffffffd20f40ea67f3bfbfffa907fbfdfffffffffff483d03a99fcefefffeb79ed9ffcfb14d4fff5bcf6cffe7d8a6a7

def w32 : Nat := 0x20000000000000000015200080000000000008000000000000000005480020000000000002a56c15fe00007c000152b60aff00003e00019b38a0000000000000cc1c567fdfee00000066ce280000000000003307159ff7fb80000019b382cff801dff03fecd9c167fc00eff81ff00000018080000000000200000000000004000000006020000000000080000000000001000004a0162a802400000002500b15401200000011aa0100800000000000d503d15880c00400046a80402000000000003540f456203001000108202200104a1290008410110008250948

def w33 : Nat := 0x200000000000000000152000800000000000080000000000000000054800e0000000000002bd6c15fe000ffc000152b63fffff87fe00019b38e0000000000000cc1c767fdffe00000066fff80000000000003f1fffffffff80000019bf86fff803ffffffefffc3fffc01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w34 : Nat := 0x20000000000000000015200080000000000008000000000000000007f800e0000000000002a7fe1fffff0ffc0001ffff3fffff87fe00019b3fa0000000000000cc1fd67fffee00000067ce28000000000000330717ffffff80000019f382cff801ffffffecd9c1fffc01fffffff00000018080000000000200000000000006000000006030000000000080000002000001800004a0166ea06410100002500b35d03208080011ba0100800000000000dd03d15880c00400046a80402000000000003542fc56603101000108202200104e32b0008410930018275958

def w35 : Nat := 0x20000000000000000015e00080000000000008000000000000000005780020000000000002a57e15ffff007c000152bf0affff803e0001ffffe0000000000000cc7ff7fffffe0000007ffff8000000000000331ffdffffff80000019b386cff803dfffffecd9c367fc01effffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w36 : Nat := 0x2246011fe00007c0001123008ff00003e00008918047f80001f0000448c023fc0000f80002246011fe00007c0001123008ff00003e00008918047f80001f0000448c023fc0000f80002246011fe00007c0001123008ff00003e00008918047f80001f0000448c023fc0000f8000ffefafbebac4b6c4a4fff7d7df5d625b62527ffbebefaeb12db1293ffdf5f7d75896d8949ffefafbebac4b6c4a4fff7d7df5d625b62527ffbebefaeb12db1293ffdf5f7d75896d8949ffefafbebac4b6c4a4fff7d7df5d625b62527ffbebefaeb12db1293ffdf5f7d75896d8949

def w37 : Nat := 0x2246211feff007c0001123108ff7f803e00008b18047f8001ff03fe448c067fdfeeff81ff22c6011fe0007fc0ff9123019ff7fbbfe07fc8918047f80001f0000448c023fc0000f80002256c15fe00007c000152b60aff00003e0000895b057f80001f000054ad82bfc0000f8000ffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afaffffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959

def w38 : Nat := 0x2a56c0000000000000150b60aff0000000000a95b00000000000000542d82bfc0000000002a56015fe00007c000152b00aff00003e0001800000000000000000cd800600000000000060000000000000000033600180000000000019b388cffbfc1ff0000cd9c467fdfe0ff80000056f8040200000000000b7c2fc5660310100015be0100800000000002df0bf15980c404000521849800c13acac00290c24c00609d6560000000603000000000008000000200000180000000180c00000000002000000080000060000128059be819040400009402cdf40c82020

def w39 : Nat := 0x2a56c15fe00007c000152b60aff00003e0000a95b057f80001f000054ad82bfc0000f80002a56c15fe00007c000152b60aff00003e00019b38acffbfddff03fecd9c567fdfeeff81ff66ce2b3feff77fc0ffb367159ff7fbbfe07fd9b38acffbfddff03fecd9c567fdfeeff81ffffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567ffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabeb

def w40 : Nat := 0x2a56d95fe00f07ffff952b6caff00783ffffca9ffe7fffffffffffe7fffffffffffffffff2a7ff9ffffffffffff9fffffffffffffffffd9b3facffffddff03fecd9fd67fffeeff81ff67ce2b3feff7ffffffb36717ffffffffffffd9f38acffbfdffffffecd9c5fffffffffffffffffffffbadfbfefefffffffffdd6fdff7f7ffffffffffbfffffefffffffffff7fffffffffffffffffeffffffbffffffffffdfffffffffffbfbefbffdffb5fdfffdfdf7dffeffdafefffefafbefff7ffdffffff7d7fffffffffffffffbebefbffdfff7fffffdf5fffffffffffff

def w41 : Nat := 0x2a57e0000000000000150bf0affff80000000af5b00000000000000542d8ffffffe0000002bd6015fe000ffffff952b03fff007ffffffd800000000000000000cd80060000000000006000000000000000003fe00380000000000019bff8fffffc3ff0000ffffcfffffe1ff80000056f8040200000000000b7c2fc5660310100015be0100800000000002df0bf15980c404000521849800c13acac00290c24c00609d6560000000603000000000008000000200000180000000180c00000000002000000080000060000128059be819040400009402cdf40c82020

def w42 : Nat := 0x2a57e15ffff007c000152bf0affff803e0000af5b057f8003fffffe54ad8fffffffffffff2bd6c15fe000ffffff952b63ffffffffffffd9b38ecffbffdfffffecd9c767fdffeffffff66fffbffffffffffffbfffffffffffffffffd9bffeffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def w43 : Nat := 0x66ce2b3feff77fc0ffb367159ff7fbbfe07fd9b38acffbfddff03fecd9c567fdfeeff81ff66ce2b3feff77fc0ffb367159ff7fbbfe07fca95b057f80001f000054ad82bfc0000f80002a56c15fe00007c000152b60aff00003e0000a95b057f80001f000054ad82bfc0000f8000ffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afaffffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959

def w44 : Nat := 0x6edeeb7feff77fc0ffb76f75bff7fbbfe07fdbb7badffbfddff03feddbdd6ffdfeeff81ff6edeeb7feff77fc0ffb76f75bff7fbbfe07fdbb7badffbfddff03feddbdd6ffdfeeff81ff6edeeb7feff77fc0ffb76f75bff7fbbfe07fdbb7badffbfddff03feddbdd6ffdfeeff81fffffffffffffdfffdfdfffffffffffefffefeffffffffffff7fff7f7fffffffffffbfffbfbfffffffffffdfffdfdfffffffffffefffefeffffffffffff7fff7f7fffffffffffbfffbfbfffffffffffdfffdfdfffffffffffefffefeffffffffffff7fff7f7fffffffffffbfffbfb

def w45 : Nat := 0x80000000000000000040000000000000000020000000000000000013200080000000000008000000000000000004c8002000000000000350a4e0000000000001a85270000000000000d5a8180000000000006a140f500007800000356a060000000000001a8503d40001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w46 : Nat := 0x8000000000000000004880020000000000002000000000000000001220008000000000000912104801000800000489082400800400000244844000000000000120422900201000000091211000000000000048108a400804000000244805200002200fc01224029000011007e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w47 : Nat := 0x8000000000000000004c00020000000000002000000000000000001300008000000000000993004c000008000004c98026000004000003000000000000000001a8000c000000000000c000000000000000006a0003000000000000356a01a800003e00001ab500d400001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w48 : Nat := 0x8000000000000000004c800000000000000020000000000000000013200080000000000009931c00000000000004c18e26008000000003560000000000000001800000000000000000d5a9200000000000006a1493500ff80000003000000000000000001ab000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w49 : Nat := 0x8000000000000000004c800200000000000020000000000000000013200080000000000009931c4c010008000004c98e2600800400000356a4e0000000000001a8527d403ffe000000d5a9380000000000006a149f500fff800000356a07a80003fe0ffffab503d40001ff07fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w50 : Nat := 0x800007ffffffffffffcce0020000007fffffe00001fffffffffffff338008000001ffffff9931e4c01ff08000004c98f2600ff840000037fffffffffffffffffa87ffdffffffffffffdfffffffffffffffffea1fff7ffffffffffff56a07a80003fe0ffffab503d40001ff07fffffa907fbfdfffffffffff483d03a99fcefefffea41feff7ffffffffffd20f40ea67f3bfbfffade7b67ff3ec5353ffd6f3db3ff9f629a9fffffff9fcfffffffffff7ffffffdfffffe7fffffffe7f3ffffffffffdfffffff7fffff9ffffed7fa6417e6fbfbffff6bfd320bf37dfdf

def w51 : Nat := 0x80001800000f003fffcc800e000007801fffe00ffe3ffffffffffff3fffffffffffffffff993ffcffffffffffffcffffffffffffffffff56a7e0007fc0000001a853fd403ffe000000d5e938000000ffffffea149ffffffffffffff57a07a80003fffffffab503ffffffffffffffffb5fe9905f9befeffffdaff4c82fcdf7f7ffefffffffbfffffcffffffffcfe7ffffffffffbffffffeffffff3ffffffff3f9ffffffffffeb79ed9ffcfb14d4fff5bcf6cffe7d8a6a7ffe907a07533f9dfdfffd483fdfefffffffffffa41e81d4cfe77f7fff520ff7fbffffffff

def w52 : Nat := 0x8001e0001ff00000004c80f2000ff80000002070000000003ffffff32000fffffffffffff99f1c4c01000ffffffcc98e3fffffffffffff56a4e000003c00ffffa8527d403ffe007fffd5bff8ffffffffffffeffffffffffffffffff56fffbffffffffffffbfffffffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w53 : Nat := 0x912114801008803f0048908a400804401f80244845200402200fc01224229002011007e00912114801008803f0048908a400804401f80244845200402200fc01224229002011007e00912114801008803f0048908a400804401f80244845200402200fc01224229002011007e00000000000002000202000000000001000101000000000000800080800000000000400040400000000000200020200000000000100010100000000000080008080000000000040004040000000000020002020000000000010001010000000000008000808000000000004000404

def w54 : Nat := 0x912114801008803f004c908a400804401f80244845200402200fc01324229002011007e009931d4c01008803f004c98ea600804401f80356a4f200402200fc01aa527d403fff007e00d5a93c801008803f006a949f500fffc01f80356a47a80403fe0ffffab523d40201ff07fff000000000002000202000000000001000101000000000000800080800000000000400040400000000000200020200000000000100010100000000000080008080000000000040004040000000000020002020000000000010001010000000000008000808000000000004000404

def w55 : Nat := 0x9831d00000000000004c18e8000000000000264c0400000000000013060298000100000009930100000000000004c180a6000040000003000000000000000001800000000000000000c000000000000000006ac0030000000000003000000000000000001ab000c000000000000001050000000000000000828000000000000000404000000000000000202082001000400000101000000000000000080820800400100000000000000000000000000000000000000000000000004000000000000000000800000000000000001000000000000000000200000000

def w56 : Nat := 0x9900040000000000004c8002000000000000264c7130040020000013263898020010000009931c4c010008000004c98e2600800400000356a4fa807ffc000001ab527d403ffe000000d5a93ea0000ff83fffead49f500ffffc1ffff56a4fa80003fe0ffffab527d403ffff07fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w57 : Nat := 0x993014c00008803f004c980a600004401f80260c7530040200000013263a00000000000009831d4c010080000004c98e8000000000000356a49a807fc3e00001ab524d403fe1f00000d58006000000000000600000000000000000356001800000000000180000000000000000000101041000801280800080820800400940400041410400200080000020a00000000000000010504100080020000008280000000000000000000011481004040000000008a408020200000000001000000400000000002000000000000000000400000100000000000800000000

def w58 : Nat := 0x9931c4c010008000004c98e26008004000002640010000000000001000000000000000000990004000000000000400000000000000000356a07a80003fe0ffffab503d40001ff07fffd4293ea01fff0000006ad49c000000000000350a4fa807ffc000001ab5270000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w59 : Nat := 0x9931c4c010008000004c98e2600800400000264c7130040020000013263898020010000009931c4c010008000004c98e2600800400000356a4fa807fffe0ffffab527d403ffff07fffd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffab527d403ffff07fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w60 : Nat := 0x9931d00000000000004c18ea600804000000264c7400000000000013063a9802010000000993014c00008803f004c980a600004401f803000000000000000001ab000c000000000000c000000000000000006ac003000000000000356a49a807fc3e00001ab524d403fe1f0000000105000000000000000082820800400100000041400000000000000020a082001000400000101041000801280800080820800400940400000000010000000000000000002000000800000000004000000000000000000800000200000000011481004040000000008a40802020

def w61 : Nat := 0x9931d00000000000004c98ea600804000000264c7400000000000013263a98020100000009931d4c01008803f004c98ea600804401f80356a4e0000000000001ab527d403ffe000000d5a9380000000000006ad49f500fff800000356a4fa807fffe0ffffab527d403ffff07fff00105000000000000000082820800400100000041400000000000000020a082001000400000101041000801280800080820800400940400000000010000000000000000002000000800000000004000000000000000000800000200000000011481004040000000008a40802020

def w62 : Nat := 0x9931d40000000000004c18ea600804000000264c7530040020000013263a9802011000000993014c00008803f004c980a600004401f80350a4fa807ffc000001ab527c000000000000d5a81ea0000ff83fffead40f500007fc1ffff56a4fa807fc3e00001ab527d403ffff0000000105000000000000000082820800400100000041400000000000000020a082001000400000101041000801280800080820800400940400000000010000000000000000002000000800000000004000000000000000000800000200000000011481004040000000008a40802020

def w63 : Nat := 0x9931d4801008803f004c98ea600804401f80264c75200402200fc013263a9802011007e00993114c01008803f004c988a600804401f80344845200402200fc01ab422d002011007e00d12114801008803f006ad08b400804401f80356a4da807fe3e0fc01ab526d403ff1f07e0000105000000200020200082820800500110100041400000080008080020a082001400440400101041000a012a0a00080820800500950500000000010080008080000000002040004840000000004020002020000000000810001210000000011489004848000000008a44802424

def w64 : Nat := 0x9931d4c010080000004c98ea600804000000264c75300002200fc013263a9802011007e009931d4c00008803f004c98ea600804401f803560018000000000001ab000c000000000000d5a926a01ff0f800006ad493500ff87c0000356a49a807fc3e00001ab524d403fe1f00000001050410008002000000828208004001000000414104002004a0200020a08200100250100010504100080128080008282080040094040000000001400000100000000000a000000800000000045204010100000000022902008280000000011481004040000000008a408020a0

def w65 : Nat := 0x9931d4c01008803f004c98ea600804401f80264c75300402200fc013263a9802011007e009931d4c01008803f004c98ea600804401f80356a4fa807fffe0ffffab527d403ffff07fffd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffab527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w66 : Nat := 0x9931dcc0100f803fffcc98ee600807c01fffe64fff3ffffffffffff3fffffffffffffffff993ffcffffffffffffcffffffffffffffffff56a7fa807fffe0ffffab53fd403ffff07fffd5e93ea01fffffffffead49ffffffffffffff57a4fa807fffffffffab527ffffffffffffffffb5fe9905f9befeffffdaff4c82fcdf7f7ffefffffffbfffffcffffffffcfe7ffffffffffbffffffeffffff3ffffffff3f9ffffffffffeb79ed9ffcfb14d4fff5bcf6cffe7d8a6a7ffe907a07533f9dfdfffd483fdfefffffffffffa41e81d4cfe77f7fff520ff7fbffffffff

def w67 : Nat := 0x9931f0001ff00000004c18fa600ffc000000267c740000003ffffff3063afffffffffffff99f014c00008ffffffcc980bfffffffffffff00006000003c00ffffab003c00001e007fffc03ff8ffffffffffffeffffffffffffffffff56fffbffffffffffffbfffffffffffffffffffbdf7b67ff3ec5353ffdefbfbbffdf639a9fffe55e81d4cfe77f7fff72aff7fbfffffffffff917e1753bf9ffdfffdc8bfdfefffffffffffed7fa6517e6fbfbffff6bfd322bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffffffffcffffffffcfefffffffff

def w68 : Nat := 0x9931f4c01ff8803f004c98fa600ffc401f80267c753004023ffffff3263afffffffffffff99f1d4c01008ffffffcc98ebfffffffffffff56a4fa807fffe0ffffab527d403ffff07fffd5bffeffffffffffffeffffffffffffffffff56fffbffffffffffffbfffffffffffffffffffbdf7f77ffbed7b5bffdefbfbbffdf6bdadfffe55f85d4efe7ff7fff72aff7fbfffffffffff957e1753bf9ffdfffdcabfdfefffffffffffed7fa755ff6ffffffff6bfd3aaffb7ffffffbfffffffffffff7ffffffff3fbffffffffffefffffffffffffdffffffffcfefffffffff

def w69 : Nat := 0xa000000000000000005da002800000000000280000000000000000176800a000000000000bb77c5dff00087c0005dbbe2eff80043e0003dfbce0000000000001ec5e7f7ffffe000000f7ef380000000000007b179fdfffff8000003dfb87eff803fffffffefdc3f7fc01fffffff00000018080000000000200000000000004000000006020000000000080000000000001000004a0162a802400000002500b15401200000011aa0100800000000000d503d15880c00400046a80402000000000003540f456203001000108202200104a1290008410110008250948

def w70 : Nat := 0xaa56c15fe00007c0005dab62aff00003e0002a95b057f80001f000176ad8abfc0000f8000bb77c5dff00087c0005dbbe2eff80043e0003dfbcecffbfddff03ffedde7f7ffffeff81fff7ef3b3feff77fc0fffb779fdfffffbfe07ffdfb8feffbfffffffffefdc7f7fdfffffffffffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567ffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabeb

def w71 : Nat := 0xbb77d5dff00887ff005dbbeaeff80443ff802eddf577fc0221ffc0176efabbfe0110ffe00bb77d5dff00887ff005dbbeaeff80443ff803dfbcfeffffffffffffefde7f7ffffffffffff7ef3fbffffffffffffbf79fdffffffffffffdfbcfeffffffffffffefde7f7fffffffffffffffffffbaceb7eeaeffffffffdd675bf7577fffffffeeb3adfbabbffffffff759d6fdd5dffffffffbaceb7eeaeffffffffdd675bf7577ffbebefbffdffb5fdfffdf5f7dffeffdafefffefafbefff7fed7f7fff7d7df7ffbff6bfbfffbebefbffdffb5fdfffdf5f7dffeffdafef

def w72 : Nat := 0xc000000000000000006ac0030000000000003000000000000000001ab000c000000000000d5a926a01ff0f800006ad493500ff87c0000264c7400000000000013063a98020100000009931d00000000000004c18ea600804000000264c05300002200fc01326029800011007e00000000000400000000000000000080000020000000000100000000000000000020000008000000000452040101000000000229020080800041400000000000000020a0820010004000001050000000000000000828208004001000000404104002004a020002020820010025010

def w73 : Nat := 0xc000000000000000006ec0030000000000003000000000000000001bb000c000000000000ddb9e6e01ff0f800006edcf3700ff87c0000376e7e0000000000001b873fdc03ffe000000ddb9f80000000000006e1cff700fff800000376e07b80003fe0ffffbb703dc0001ff07fff000000000400000000000000000080000020000000000100000000000000000020000008000000000452040101000000000229020080800041400000000000000020a0820010004000001050000000000000000828208004001000000404104002004a020002020820010025010

def w74 : Nat := 0xd5a81ea0000ff83fffead40f500007fc1ffff50a4fa807ffc000001ab5270000000000000d4293ea01fff0000006ad49c000000000000264c7130040020000013263898020010000009900040000000000004000000000000000002640010000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w75 : Nat := 0xd5a926a01ff0f800006ad493500ff87c00003560018000000000001800000000000000000d58006000000000000600000000000000000264c05300002200fc01326029800011007e009831d4c010080000004c98e8000000000000260c7530040200000013263a00000000000000000000045204010100000000022902008080000000000400000100000000000800000000000000000100000040000000000200000000000404104002004a02000202082001002501000105041000800200000082800000000000000041410400200080000020a0000000000000

def w76 : Nat := 0xd5a9380000000000006a149f500fff800000356a4e0000000000001a8527d403ffe000000d5a81ea0000ff83fffead40f500007fc1fffe0000000000000000013200080000000000008000000000000000004c8002000000000000264c713004002000001326389802001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w77 : Nat := 0xd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffab527d403ffff07fffd5a93ea01ffff83fffead49f500ffffc1fffe64c75300402200fc013263a9802011007e009931d4c01008803f004c98ea600804401f80264c75300402200fc013263a9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w78 : Nat := 0xd5a93ea01ffff83fffead49f500ffffc1ffff56a4fa807fffe0ffffbb527d403ffff07fffd5a93ea01ffff83fffeed49f500ffffc1ffff74e7f300402200fc01ba73f9802011007e00ddb9dcc01008803f006e9cef700807c01f80376e77300402200fc01ba73bdc0201f007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w79 : Nat := 0xd5a93ea01ffff83fffeed49f500ffffc1ffff56a4fa807fffe0ffffbb527d403ffff07fffddb93ee01ffff83fffeedc9f700ffffc1ffff64c75300402200fc01ba63ad802011007e00d931d4c01008803f006e98eb600804401f80376e75b804023e0fc01bb73adc02011f07e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w80 : Nat := 0xd5a93ea01ffff83fffeed49f500ffffc1ffff56a4fa807fffe0ffffbb527d403ffff07fffddb9fea01ffff83fffeedcff700ffffc1ffff76c75300402200fc01b263a9802011007e00ddb9f4c01008803f006e9cfb700ffc401f80364c75300402200fc01bb63ad802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w81 : Nat := 0xd5a93ea01ffff83fffeed49f500ffffc1ffff56a4fa807fffe0ffffbb527d403ffff07fffddb9fee01ffff83fffeedcff700ffffc1ffff76e7f300402200fc01ba73fdc03fff007e00ddb9fcc01008803f006e9cff700fffc01f80376e77b80403fe0ffffbb73bdc0201ff07fff000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w82 : Nat := 0xd5a9fea01ffff83fffead4ff500ffffc1ffff57a4fa807fffffffffab527fffffffffffffd5e93ea01fffffffffead49fffffffffffffe64c77300403e00ffff3263b980201f007fff993ffcffffffffffffcfffffffffffffffffe64fff3ffffffffffff3fffffffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w83 : Nat := 0xd931d4c01008803f006ed8eb600804401f80364c75300402200fc01bb63ad802011007e00ddb9f6e01ff8f83f006edcfb700ffc7c1f80376e7fa807fffe0ffffbb73fdc03ffff07fffddb9fea01ffff83fffeedcff700ffffc1ffff76e4fb807fffe0ffffbb727dc03ffff07fff00105041040a012a0a000828208085009525000414104102804a8280020a082021402549400105041452a413a1a00082820a295209d0d00041400114cd204d4c0020a0828a769066a600105000453348135300082820a29da419a980040410514ed24ed6c002020828a769276b6

def w84 : Nat := 0xdda93ea01ffff83fffeed49f500ffffc1ffff76e7fb807fffe0ffffbb73fdc03ffff07fffddb9fee01ffff83fffeedcff700ffffc1ffff76e7fb807ffe00fc01bb73fdc03fff007e00ddb9fee0100ff83fffeedcff700ffffc1ffff76e7fb80403fe0ffffbb73fdc03ffff07fff000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w85 : Nat := 0xddb9dee0100ff83fffeedcef700807fc1ffff74e7fb807ffe00fc01bb73f9802011007e00dd39fee01fff803f006edcfe600804401f80376e7fb807fffe0ffffbb73fdc03ffff07fffdda93ea01ffff83fffead49f500ffffc1ffff76a4fa807fffe0ffffab527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w86 : Nat := 0xddb9fcc01008803f006e9cff700fffc01f80376e7f300402200fc01ba73fdc03fff007e00ddb9dee0100ff83fffeedcef700807fc1ffff56a4fa807fffe0ffffbb527d403ffff07fffd5a93ea01ffff83fffeed49f500ffffc1ffff76e7fb807fffe0ffffbb73fdc03ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w87 : Nat := 0xddb9fee01ffff83fffeedcff700ffffc1ffff76a4fa807fffe0ffffab527d403ffff07fffdda93ea01ffff83fffead49f500ffffc1ffff76e77b80403fe0ffffbb73bdc0201ff07fffdd39fee01fff803f006edcfe600804401f80374e7fb807ffe00fc01bb73f9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w88 : Nat := 0xddb9fee01ffff83fffeedcff700ffffc1ffff76e7fb807fffe0ffffbb73fdc03ffff07fffddb9fee01ffff83fffeedcff700ffffc1ffff76e7fb807fffe0ffffbb73fdc03ffff07fffddb9fee01ffff83fffeedcff700ffffc1ffff76e7fb807fffe0ffffbb73fdc03ffff07fff00105041453b493b5b00082820a29da49dad80041410514ed24ed6c0020a0828a769276b600105041453b493b5b00082820a29da49dad80041410514ed24ed6c0020a0828a769276b600105041453b493b5b00082820a29da49dad80041410514ed24ed6c0020a0828a769276b6

def w89 : Nat := 0xe000000000000000007000000000000000003800000000000000001c00000000000000000e000000000000000007000000000000000003f8f860000000000001fc7c30000000000000fe3e180000000000007f1f0c0000000000003f8f860000000000001fc7c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000486000000000000000243000000000000000121800000000000000090c0000000000000004860000000000000002430000000000000

def w90 : Nat := 0xe000000000000000007000000000000000003800000000000000001fc000e000000000000e000000000000000007fe0038000000000003800000000000000001fc0000000000000000e000000000000000007f00038000000000003fff800000000000001fc7c0fffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w91 : Nat := 0xe000000000000000007000000000000000003800000000000000001ff8000000000000000e000000000000000007fe0000000000000003f8ff80000000000001fc7fc0000000000000ffc0000000000000007000000000000000003ff0000000000000001c00000000000000000000000000000000000000000000000000000000000040200000000000000000000000000000000010080000000000000000000000000000012801008000000000009400804000000000040000000000000000000000400000000000010000000000000000000000100000000000

def w92 : Nat := 0xe000000000000000007000000000000000003800000000000000001ff800e000000000000e000000000000000007fe0038000000000003f8ffe0000000000001fc7ff0000000000000fffe180000000000007f1f0ffff0078000003fff860000000000001fc7c3fffc01e0000000000000000000000000000000000000000000000000403000000000000000000200000000000000100c000000000000000000800000000005be0100800000000002df008040000000000521800000000000000090c24c0060110100014860000000000000002430930018044040

def w93 : Nat := 0xe000000000000000007ac0030000000000003800000000000000001ff800e000000000000f5a926a01ff0f800007ff493d00ff87c00003fcffe0000000000001fc7ff9802010000000ffffd80000000000007f1feffff8078000003fff87300002200fc01fe7c3fffc01f007e000000000004000000000000000000800000200000000403000000000000000000200000080000000104d204010100000000022902008080005be0100800000000002df08a041000400000525800000000000000092c24c006011010001486104002004a020002430930018065050

def w94 : Nat := 0xe000000000000000007c80020000000000003800000000000000001ff800e000000000000f931c4c010008000007ff8e3e008004000003feffe0000000000001fc7ffd403ffe000000ffff380000000000007f1f9fffffff8000003fff87a80003fe0ffffff7c3fffc01ff07fff0000000000000000000000000000000000000000000403000000000000000000200000000000000100c000000000000000000800000000005be0100800000000002df008040000000000521800000000000000090c24c0060110100014860000000000000002430930018044040

def w95 : Nat := 0xe000000000000000007f00038000000000003800000000000000001fc000e000000000000fffe07ffe000ffc0007fff03fff0007fe0003800000000000000001fc000e000000000000e000000000000000007f00038000000000003fff81fff8003ff0001fffc0fffc001ff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w96 : Nat := 0xe000000000000000007f00038000000000003800000000000000001ff800e000000000000fffe07ffe000ffc0007fff03fff0007fe0003f8ffe0000000000001fc7ffe000000000000fffe180000000000007f1f0ffff0078000003fff87fff8003ff0001fffc3fffc01fff80000000000000000000000000000000000000000000000403000000000000000000200000000000000100c000000000000000000800000000005be0100800000000002df008040000000000521800000000000000090c24c0060110100014860000000000000002430930018044040

def w97 : Nat := 0xe000000000000000007f80038000000000003800000000000000001fe000e000000000000ffffc7fff000ffc0007fffe3fff8007fe0003d6a4e0000000000001fc527f403ffe000000f5a9380000000000007f149fd00fff8000003fff87fff803ffffffffffc3fffc01fffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w98 : Nat := 0xe000000000000000007f80038000000000003800000000000000001ff800e000000000000ffffc7fff000ffc0007fffe3fff8007fe0003feffe0000000000001fc7fff403ffe000000ffff380000000000007f1f9fffffff8000003fff87fff803ffffffffffc3fffc01fffffff0000000000000000000000000000000000000000000403000000000000000000200000000000000100c000000000000000000800000000005be0100800000000002df008040000000000521800000000000000090c24c0060110100014860000000000000002430930018044040

def w99 : Nat := 0xe000000000000000007fc0038000000000003800000000000000001ff000e000000000000ffff27fffff0ffc0007fff93fffff87fe0003e4c740000000000001fc63af802010000000f931d00000000000007f18ebe008040000003fff85fff8023fffc01fffc2fffc011fffe00000000000400000000000000000080000020000000000100000000000000000020000008000000000452040101000000000229020080800041400000000000000020a0820010004000001050000000000000000828208004001000000404104002004a020002020820010025010

def w100 : Nat := 0xe000000000000000007fc0038000000000003800000000000000001ff000e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003f6e7e0000000000001fc73ffc03ffe000000fdb9f80000000000007f1cfff00fff8000003fff87fff803ffffffffffc3fffc01fffffff000000000400000000000000000080000020000000000100000000000000000020000008000000000452040101000000000229020080800041400000000000000020a0820010004000001050000000000000000828208004001000000404104002004a020002020820010025010

def w101 : Nat := 0xe000000000000000007fe0000000000000003800000000000000001ff800e000000000000ffffe00000000000007f1ff3fffff80000003ff0000000000000001c00000000000000000ffffe00000000000007f1ff3fffff80000003800000000000000001ff800e00000000000000000018080000000000200000000000000000000002000000000000080000000000001000004a00402000000000002500b054002000000100000000000000000000003010000000000004a00402000000000002500b05400200000000000200000000000008000000000000100

def w102 : Nat := 0xe000000000000000007fe0000000000000003800000000000000001ff800e000000000000ffffe00000000000007ffff3fffff80000003ffffe0000000000001fc7ff0000000000000fffff80000000000007f1fffffffff8000003fff860000000000001fffc3fffc01e00000000000018080000000000200000000000000000000006030000000000080000002000001000004a0140e000000000002500b05c00200000015be0100800000000002df03814000000000056b8040200000000000b5c2fc546031010001486020000000000000a430930018044140

def w103 : Nat := 0xe000000000000000007fe0020000000000003800000000000000001ff800e000000000000ffffe4c010008000007f9ff3fffff84000003ffa4e0000000000001e8527d403ffe000000fffff80000000000007f1fffffffff8000003d6a07a80003fe0ffffffd03f40001ff07fff00000018080000000000200000000000000000000002000000000000080000000000001000004a00402000000000002500b054002000000100000000000000000000003010000000000004a00402000000000002500b05400200000000000200000000000008000000000000100

def w104 : Nat := 0xe000000000000000007fe0030000000000003800000000000000001ff800e000000000000ffffe6a01ff0f800007fdff3fffff87c00003ffc740000000000001f063a9802010000000fffff00000000000007f1ffbfffffc0000003e4c05300002200fc01ffe02f800011007e00000000180c0000000000200000008000002000000002010000000000080000002000001800004a00447204010100002500b27d022080800141400000000000000020a0b210100040000014f0040200000000000a782b8544021000000404124002004a02000a020820010025110

def w105 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001c00000000000000000ffc0070000000000007000000000000000003fff860000000000001fc7c3fffc01e000000fe3ff80000000000007f1ffc0000000000003f8f87fff803c000001fffc30000000000000000000100c00000000000000000080000000000000000000000000000000000000000000000000000010000000000000008060000000000148600000000000000024309300180440400016f8040200000000000b7c020100000000000486126003008808000a430000000000000

def w106 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff8000000000000000fe3fe7fffff00000007ffff00000000000003ffff80000000000001fc7fcfffffe0000000ffc0000000000000007000000000000000003ff001c000000000001c0000000000000000000000008000000000000200000000000004000000006020000000000080000000000000000004a0160a8004000000025002010000000000012801008000000000009402c15000800000040000000000000000000000c04000000000010000000000000200000000100000000000

def w107 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffc0070000000000007fe0038000000000003ffffe0000000000001fc7fffffc01e000000fffff80000000000007f1ffffff0078000003fff87fff803c000001fffc3fffc01e000000000000100c000000000000000000800000000000000403000000000000000000200000000000000100d000000000000000806800000000015be0100800000000002df09b04180440400056f8040200000000000b7c26c106011010001486126003008808000a430930018044040

def w108 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe70000000000007f1ff3fffff80000003fff860000000000001fc7c3fffc01e000000fffff80000000000007f1ffffffff80000003f8f87fff803c000001fffc3e000000000000000000180c0000000000200000008000000000000002000000000000080000000000001000004a00403000000000002500b07400200000014860000000000000002430b310180440400016f8040200000000000b7c0b0540020000000486126003008808000a430000000000100

def w109 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe7ffe000ffc0007ffff3fffff87fe0003ff0000000000000001fc000e000000000000ffffe00000000000007f1ff3fffff80000003fff81fff8003ff0001fffc0fffc001ff800000000018080000000000200000000000000000000002000000000000080000000000001000004a00402000000000002500b054002000000100000000000000000000003010000000000004a00402000000000002500b05400200000000000200000000000008000000000000100

def w110 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe7fff000ffc0007ffff3fffff87fe0003ffa4e0000000000001fc527f403ffe000000fffff80000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffff00000018080000000000200000000000000000000002000000000000080000000000001000004a00402000000000002500b054002000000100000000000000000000003010000000000004a00402000000000002500b05400200000000000200000000000008000000000000100

def w111 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe7fffff00000007ffff3fffff80000003ffff80000000000001fc7fcfffffe0000000ffffe00000000000007f1ff3fffff80000003ff001c000000000001ff800e00000000000000000018080000000000200000000000004000000006020000000000080000000000001000004a0160a800400000002500b054002000000112801008000000000009403c15000800000044a00402000000000002500f05400200000010000200000000200008000100000000100

def w112 : Nat := 0xe000000000000000007fe0038000000000003800000000000000001ff800e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffe0000000000001fc7ffffffffe000000fffff80000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w113 : Nat := 0xe00007ffffffffffffffe0038000007ffffff80001fffffffffffffff800e000001ffffffffffe7fffff0ffc0007ffff3fffff87fe0003fffffffffffffffffffc7fffffffffffffffffffffffffffffffffff1fffffffffffffffffff87fff803ffffffffffc3fffc01fffffffffa907fbfdfffffffffff483d03a99fcefefffea41feff7ffffffffffd20f40ea67f3bfbfffade7b67ff3ec5353ffd6f3db3ff9f629a9fffffff9fcfffffffffff7ffffffdfffffe7fffffffe7f3ffffffffffdfffffff7fffff9ffffed7fa6417e6fbfbffff6bfd320bf37dfdf

def w114 : Nat := 0xe0001800000f003fffffe00f800007801ffff80ffe3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fc0000001fc7ffffffffe000000fffff8000000ffffffff1fffffffffffffffffff87fff803ffffffffffc3ffffffffffffffffb5ff99c5f9befeffffdaff4c8afcdf7f7ffefffffffbfffffcffffffffcfe7ffffffffffbfffffffffffff3ffffffffbffffffffffffffffed9ffcfb14d4fff7fffffffffdce6e7ffffffa47733f9dfdfffdffffffffffffffffffec7fa7d4ffeffffffff63ff7fbffffffff

def w115 : Nat := 0xe001e00000000000007f00f3800ff80000003870000000000000001fc000ffffffe000000fffe07ffe000ffffffffff03fff007fffffff800000000000000001fc000e000000000000e000000000000000007fe0038000000000003ffff9fffffc3ff0001ffffcfffffe1ff80000004e00402000000000002700b05600200000010000000000000000000000b711980c4040004000000000118c8c00000024c00609d6560000000200000000000008000000000000180000000180c00000000002000000080000060000128059ba819040400009400cc740c82020

def w116 : Nat := 0xe001e0001ff00000007f00f3800ff80000003870000000003fffffffc000ffffffffffffffffe07ffe000ffffffffff03fffffffffffff80006000003c00fffffc003e00001e007fffe03ff8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w117 : Nat := 0xe001e0001ff00000007fe0f3800ff80000003870000000003ffffffff800fffffffffffffffffe7fffff0fffffffffff3fffffffffffffffffe000003c00fffffc7ffffffffe007ffffffff8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffade7be7ff3ec5353fff6f3db3ff9f629e9fffa41ee1f4cfe77f7fffd20ff7fbffffffffffeda7b67fb3fddfdfffd6d3fffffffffffffffffffb6497e6fbfbfffffffff35bf3fdfdffffffffffeffffff3ffffffffffdffffffffffffffffffbfffffeffffffffdfe7ffffffff

def w118 : Nat := 0xe6ce2b3feff77fc0ffffe7179ff7fbbfe07ff9b38acffbfddff03ffff9c5e7fdfeeff81ffffffeffffff7ffc0fffffff7fffffbffe07ffffffe57f80001f0001fcfffffffffe0f8000fffff95fe00007c0007f3fffffffff83e0003fffb7fff803ffffffffffdbfffc01fffffffffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afaffffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959

def w119 : Nat := 0xea56c15fe00007c0007f2b63aff00003e0003a95b057f80001f0001fcad8ebfc0000f8000fffec7ffe000ffc0007fff63fff0007fe00039b38acffbfddff03fffd9c5e7fdfeeff81ffe6ce2b3feff77fc0ffff67179ff7fbbfe07fffff8bfffbfdfff03fffffc5fffdfefff81ffffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567ffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabeb

def w120 : Nat := 0xea56c15fe00007c0007feb63aff00003e0003a95b057f80001f0001ffad8ebfc0000f8000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffecffbfddff03fffdfffffffffeff81fffffffb3feff77fc0ffff7fffffffffbfe07fffff8ffffbffffffffffffc7fffdfffffffffffffffffbeccb7ecacffffffffdde65bf6767fffffffefb32dfb2b3ffffffff77996fd9d9ffffffffffecf7fcbcfffffffffff67bfe5e7fffffefbffd7fb57d7fffffffffffbfdebebffffffbefff5fed5f5fffffffffffeff7afaffffefffffff7fff7f7ffff7ffffffbfffbfb

def w121 : Nat := 0xf12114801008803f007ff08bc00804401f803c4845200402200fc01ffc22f002011007e00fffff7fffff8ffff007ffffbfffffc7fff803fffff200402200fc01fe7fffffffff007e00fffffc801008803f007f9fffffffffc01f803fffc7fffc03ffffffffffe3fffe01fffffff000000180c0200020200200000008100016100000006030080008080080000002040005840004a0166fa26412120002500b37d13209090015be0100808000808002df0bf159c0c44440056f8040202000202000b7c2fc56703111100148612600384ebab800a43093001c275d5c

def w122 : Nat := 0xf4293ea01fff0000007ff49f8000000000003d6a07a80003fe0ffffffd03f40001ff07ffffffffffffff0ffc0007fffffffffffffe0003fffff0000000000001fc7ffffffffe000000fffffcc010008000007f9fffffffffc000003fff87fff803ffffffffffc3fffc01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w123 : Nat := 0xf580060000000000007fe0038000000000003d6a49a807fc3e00001ffd24f403fe1f00000ffffe7fffff0ffc0007ffff3fffff87fe0003fffff3004020000001fe7ffffffffe000000fffffcc00008803f007f9fffffffffc01f803ffff7fff803fffffffffffbfffe01fffffff000000180d000000400020000002800000600000000613481004040008000008a408021a00004a0166fa06410100002500b37d03208280015be1140820008000002df0bf15980c40400056f8450208012808000b7c2fc56603941400149612600304eb2b000a4b0930018275958

def w124 : Nat := 0xf5a9380000000000007f149fd00fff8000003d6a4e0000000000001fc527f403ffe000000fffe1fffe00fffffffffff0ffff007fffffff800000000000000001fe000e000000000000e000000000000000007f80038000000000003ffff1fffc003ff0001ffff8fffe001ff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w125 : Nat := 0xf5a9380000000000007ff49fd00fff8000003d6a4e0000000000001ffd27f403ffe000000fffffffffffffffffffffffffffffffffffffffffe0000000000001fe7ffffffffe000000fffff80000000000007f9fffffffff8000003ffff7fffc03fffffffffffbfffe01fffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w126 : Nat := 0xf5a93ea01ffff83ffffad49f500ffffc1ffffd6a4fa807fffe0ffffeb527d403ffff07ffff5a93ea01ffff83ffffad49f500ffffc1fffffcff7300402200fc01fe7fb9802011007e00ff3fdcc01008803f007f9fee600804401f803fcff7300402200fc01fe7fb9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800496104002804a8280024b082001402541400125841000a012a0a00092c208005009505000496104002804a8280024b0820014025414

def w127 : Nat := 0xf5a93ea01ffff83ffffad49f500ffffc1ffffd6a4fa807fffe0ffffff527f403ffff07ffff5a93ea01ffff83ffffff49fd00ffffc1ffffe4c75300402200fc01fe63a9802011007e00f931d4c01008803f007f98ebe00804401f803ffff5300402200fc01fe7fafffe011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w128 : Nat := 0xf5a93ea01ffff83ffffad49f500ffffc1ffffd6a4fa807fffe0ffffffd27f403ffff07ffff5a93ea01ffff83ffffff49fd00ffffc1fffffcfff300402200fc01fe7ff9802011007e00ffffdcc01008803f007f9feffff807c01f803ffff7300402200fc01fe7fbfffe01f007e00000000004533481353000000002299a409a980000004134cd204d4c000000008a669026a6000000104d33481353000000002299a409a98005be114082804a828002df08a041402541400525841000a012a0a00092c24c007019515001496104002804a8280024b093001c065454

def w129 : Nat := 0xf5a93ea01ffff83fffffd49f500ffffc1ffffd6a4fa807fffe0ffffff527f403ffff07fffffff3ea01ffff83fffffdf9ffffffffc1ffffe4c75300402200fc01f263a9802011007e00f931d4c01008803f007f98ebe00804401f803e4c75300402200fc01ffe3af802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w130 : Nat := 0xf5a93ea01ffff83fffffd49fd00ffffc1ffffd6a4fa807fffe0ffffff527f403ffff07fffffff3fffffffffffffffff9ffffffffffffffe4c75300402200fc01fe63af802011007e00f931d4c01008803f007f98ebe00804401f803ffff5fffc023fffc01ffffafffe011fffe00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w131 : Nat := 0xf5a93ea01ffff83fffffd49fd00ffffc1ffffd6a4fa807fffe0ffffff527f403ffff07fffffffffffffffffffffffffffffffffffffffff6e7f300402200fc01fe73ffc03fff007e00fdb9fcc01008803f007f9cfff00fffc01f803ffff7fffc03fffffffffffbfffe01fffffff000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w132 : Nat := 0xf5a93ea01ffff83ffffff49fd00ffffc1ffffd6a4fa807fffe0ffffffd27f403ffff07fffffffffffffffffffffffffffffffffffffffffffff300402200fc01fe7fffffffff007e00fffffcc01008803f007f9fffffffffc01f803ffff7fffc03fffffffffffbfffe01fffffff000000184d33481353002000002299a409e980000006134cd204d4c008000008a669027a60004a0166fb36c13530002500b37d9b609a98015be114082804a828002df0bf159c0e54540056f845020a012a0a000b7c2fc56703951500149612600384ebab800a4b093001c275d5c

def w133 : Nat := 0xf831d4c010080000007ff8eb8000000000003e4c05300002200fc01ffe02f800011007e00fffff7fffff0ffc0007ffffbfffffc7fe0003fffff8000000000001fc7ffffffffe000000fffffea01ff0f800007fdffffffffffc00003fff87fff803ffffffffffc3fffc01fffffff001050590c08002000002828000080000060000404164302004a02000a0208202100251900014f0166fa0641010000a782bb7d43218080015be0100c00000100002df0bf1d980c40400056f8044720401010000b7c2fe7f623181800148612610304eb2b000a4309302182759d8

def w134 : Nat := 0xf900040000000000007fe0038000000000003e4c713004002000001ffe38f802001000000ffffe7fffff0ffc0007ffff3fffff87fe0003fffffa807ffc000001ff7ffffffffe000000fffffea0000ff83fffffdffffffffffc1fffffffcffff803ffffffffffe7fffffffffffff000000180c0000000000200000008000006000000006030000000000080000002000001800004a0166fa06410100002500b37d03208080015be0100800000000002df0bf15980c40400056f8040200000000000b7c2fc56603101000148612600304eb2b000a430930018275958

def w135 : Nat := 0xf931d00000000000007ff8ebe008040000003e4c740000000000001ffe3af802010000000fffff7fffff8ffff007ffffbfffffc7fff803ffffe0000000000001ff7ffffffffe000000fffff80000000000007fdfffffffff8000003fffcfffffffffffffffffe7fffffffffffff001050180c00000000002828208084001060000414060300000000000a0a08202100041800014b0576fa8653818000a582bb7d4329c0c0015be0101800000000002df0bf17980c40c00056f8040600000000000b7c2fc5e603103000148612714b14ef2f000a430938a58a77978

def w136 : Nat := 0xf931d4c01008803f007c98ea600804401f803e4c75300402200fc01ffe3af802011007e00f931d4c01008803f007ff8ebe00804401f803fefffa807fffe0ffffff7ffd403ffff07fffffff3ea01ffff83fffffdf9ffffffffc1fffffffcfa807fffe0ffffff7e7ffffffff07fff00105041000a012a0a000828208005009505000414144302804a8280020a0820214025414001050510c0a012a0a0008282080850095050005be0111ccd204d4c002df0088e669026a600521800453348135300090c24e29fa519b980148600114cd204d4c002430938a7e9466e6

def w137 : Nat := 0xf931d4c01008803f007f98ebe00804401f803e4c75300402200fc01fe63af802011007e00ffffd7fff008ffff007fffebfff8047fff803d6a4fa807fffe0ffffff527f403ffff07ffff5a93ea01ffff83fffffd49fd00ffffc1fffffffcfffffffffffffffffe7fffffffffffff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w138 : Nat := 0xf931d4c01008803f007ff8ea600804401f803e4c75300402200fc01ffe3af802011007e00fffff4c01008803f007f9ffbfffffc401f803ffa4fa807fffe0ffffeb527d403ffff07ffffffffea01ffff83fffffdffffffffffc1ffffd6a4fa807fffe0ffffffd27f403ffff07fff00105059080a012a0a002828208005009505000414124002804a82800a0a08200140255140014f045020a012a0a000a782b854502950500100000114cd204d4c000000309a669026a60004a00447334813530002500b27d9a609a980000002114cd204d4c008000008a669027a6

def w139 : Nat := 0xf931d4c01008803f007ff8ebe00804401f803e4c75300402200fc01ffe3af802011007e00fffff7fffff8ffff007ffffbfffffc7fff803fffffa807fffe0ffffff7ffffffffff07ffffffffea01ffff83fffffdffffffffffc1fffffffcfffffffffffffffffe7fffffffffffff001050590c0a012a0a002828208085009565000414164302804a82800a0a08202140255940014f0576faa653a1a000a782bb7d5329d0d0015be0111ccd204d4c002df0bf9ffe9c66e60056f8044733481353000b7c2fe7ffa719b980148612714fd6efffc00a430938a7eb77ffe

def w140 : Nat := 0xfdb9fee01ffff83ffffffcfff00ffffc1fffff6e7fb807fffe0fffffff3ffc03ffff07fffffffffffffffffffffffffffffffffffffffffffffb807fffe0ffffff7ffffffffff07ffffffffee01ffff83fffffdffffffffffc1ffffffffffffffffffffffffffffffffffffffff001050594d3b493b5b00282820a29da49ded80041416534ed24ed6c00a0a0828a769277b60014f0576fbb6d3b5b000a782bb7ddb69dad8015be1151ced24ed6c002df0bf9ffe9e76f60056f845473b493b5b000b7c2fe7ffa79dbd80149612714fd6efffc00a4b0938a7eb77ffe

def w141 : Nat := 0xfe3ff80000000000007f1ffc0000000000003fff860000000000001fc7c3fffc01e000000fffe180000000000007f1f0ffff0078000003800000000000000001c00000000000000000e000000000000000007fe0038000000000003800000000000000001ff800e0000000000000016f8040200000000000b7c020100000000001486000000000000000243093001804404000521800000000000000090c24c0060110100000000000000000000000000000000000000000000100c000000000000000000800000000000000403000000000000000000200000000

def w142 : Nat := 0xfe3fffffffff0000007ffffc0000000000003fff87fff803ffffffffffc3fffc01ffffffffffff80000000000007f1fffffffff8000003ff001c000000000001c00000000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003800000000000000001ff800e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w143 : Nat := 0xfe3fffffffff0000007ffffe0000000000003fff87fff803ffffffffffc3fffc01ffffffffffffcc010008000007f9fffffffffc000003ffa4fc000000000001e8527d403ffe000000fffffffffff0ffc0007fffffffffffffe0003d6a07a80003fe0ffffffd03f40001ff07fff0016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w144 : Nat := 0xfe3fffffffff0000007fffff8000000000003fff87fff803ffffffffffc3fffc01fffffffffffffffe000ffc0007fffffffffffffe0003ff001c000000000001fc000e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003fff81fff8003ff0001fffc0fffc001ff80000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w145 : Nat := 0xfe3fffffffff0000007fffff8000000000003fff87fff803ffffffffffc3fffc01ffffffffffffffffff0ffc0007fffffffffffffe0003fffffc000000000001fc7ffffffffe000000fffffffffff0ffc0007fffffffffffffe0003fff87fff803ffffffffffc3fffc01fffffff0016f85f8ecc062020002b7c02018000006000148616630304eb2b000a4309302182759d80056f8166fa0641010000b7c2ff7f63318180015be0100c00000300002df0bf1d980c40400056f8166fa0641010000b7c2ff7f633181800148616630304eb2b000a4309302182759d8

def w146 : Nat := 0xff3fffffffff0000007ffffc0000000000003ffff7fffc03fffffffffffbfffe01ffffffffffff80000000000007f9fffffffff8000003ffa4fe807ffc000001eb5270000000000000fffffffffffffffffffffffffffffffffffffd6a4e0000000000001ffd27f403ffe0000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w147 : Nat := 0xff3fffffffff0000007ffffe6008040000003ffff7fff803fffffffffffbfffe01ffffffffffffcc00008803f007f9fffffffffc01f803ff001c000000000001eb000c000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003d6a49a807fc3e00001ffd24f403fe1f000000016f85f8acc062020002b7c22810400100000149612600304eb2b000a4b09300182759580056f8450208012808000b7c2fc5660394140010000001400000300000000301a000000800004a0166fa06410100002500b37d03208280000000613481004040008000008a408021a0

def w148 : Nat := 0xff3fffffffff8000007ffffe6008004000003fff87fff803ffffffffffc3fffc01ffffffffffffc0000000000007f1fffffffff8000003ffa07e80003fe0ffffeb503d40001ff07fffffffffffffffffc0007ffffffffff87fe0003d0a4fa807ffc000001ffd27e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w149 : Nat := 0xff3fffffffff803f007ffffe600004401f803ffff7fffc03fffffffffffbfffc01ffffffffffffcc010080000007f9fffffffff8000003ffa49e807fc3e00001eb524d403fe1f00000ffffe7fffff0ffc0007ffff3fffff87fe0003d60018000000000001ff800e0000000000000016f85f8acc072828002b7c22810400940400149612600304eb2b000a4b09300182759580056f8450208002000000b7c2fc5660310100010000011481004340000000309a408020200004a0166fa06410500002500b37d03208080000000603400000100008000000a00000180

def w150 : Nat := 0xff3fffffffff803f007ffffe600804401f803ffff7fffc03fffffffffffbfffe01ffffffffffffcc01008803f007f9fffffffffc01f803ffa4fe807fffe0ffffeb527d403ffff07ffffffffffffffffffffffffffffffffffffffffd6a4fa807fffe0ffffffd27f403ffff07fff0016f85f8ace072a2a002b7c22810500950500149612600384ebab800a4b093001c275d5c0056f845020a012a0a000b7c2fc56703951500100000114cd204f4c000000309a669026a60004a0166fb36c13530002500b37d9b609a980000006134cd204d4c008000008a669027a6

def w151 : Nat := 0xffa93fa01ffff83ffffad49f500ffffc1fffffffffffffffffffffffffffffffffffffffff5a93ea01ffff83fffffd49fd00ffffc1fffffce7ff807ffe00fc01fb73f9802011007e00ffffdffff00fffffffffffeffff807ffffffff6e7f300402200fc01fe73ffc03fff007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w152 : Nat := 0xffbfffffffff0000007fffff500fff8000003fffcffff803ffffffffffe7ffffffffffffffffffea0000ff83fffffdffffffffffc1ffffff001c000000000001f20008000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003e4c713004002000001ffe38f8020010000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w153 : Nat := 0xffbffffffffff83fffffffff500007fc1fffffffcfffffffffffffffffe7fffc01ffffffffffffea01fff0000007fdfffffffff8000003ffc71f004002000001f26389802001000000ffffe7fffff0ffc0007ffff3fffff87fe0003e40010000000000001ff800e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w154 : Nat := 0xffc0000000000000007fe0038000000000003ffff80000000000001ffffcfffffe0000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffe0000000000001fffffffffffe000000fffff80000000000007fffffffffff8000003ffffffff803fffffffffffffffffffffffff004000180c000000000020000c048000006000012807038000000000089402c17000801800004a01e6fa06410100022500b37d03208480015be070280000000000adf0bf15980c40400056f80c0200000000002b7c2fc5660310500015ae13608304eb2b000ad70bf15182f5958

def w155 : Nat := 0xffc0070000000000007000000000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000e000000000000000007fe0038000000000003f8fffffffffc000001fffff0000000000000fffe1fffe00fffffffffff0ffff007fffffffffffe0000000000001fc7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w156 : Nat := 0xffc0070000000000007ac0030000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000f5a926a01ff0f800007ff493d00ff87c00003fcfffffffffc000001fffff9802010000000ffffdfffe00fffffffffffeffff807ffffffffffff300002200fc01fe7fffffffff007e000040000005000000c00000000c0680000020000128059be819040400009402cdf40c820a0000000184d204010100020000022902008680005be17e2b3018808000adf08a041000400000525849800c13acac00292c24c00609d6560015be114082004a020002df0bf15980e5050

def w157 : Nat := 0xffc0070000000000007c80020000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000f931c4c010008000007ff8e3e008004000003fefffffffffc000001fffffd403ffe000000ffff3fffe00fffffffffff9fffffffffffffffffffa80003fe0ffffff7ffffffffff07fff0040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w158 : Nat := 0xffc0070000000000007f00038000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000fffe07ffe000ffc0007fff03fff0007fe0003f8fffffffffc000001fffffe000000000000fffe1fffe00fffffffffff0ffff007fffffffffffffff8003ff0001ffffffffffffff80000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w159 : Nat := 0xffc0070000000000007fe0038000000000003f8ff9fffffc0000001ffffce000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffffffffc0000001fffffffffffe000000ffffff0000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffff004000180c000000800020000400800000600001280783a001000000089400806000001800004a01e6fa06410100022500b37d03208080015be0582a00100000002df0bf15980c40400056f8040200000080000b7c2fc56603101000148612600304eb2b000a430b31018275958

def w160 : Nat := 0xffc0070000000000007fe0038000000000003ff001c000000000001ff800e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffffff803c000001fffffffffffe000000ffffffffe00f0000007fffffffffff8000003ffffffff803fffffffffffffffc01fffffff000000180d000000000020000806800000600000000603400000000008000201a000001800004a0166fa06410100002500b37d03208080015be136083008808000adf0bf15980c40400056f84d820c022020002b7c2fc5660310100015be13608304eb2b000adf09b0418275958

def w161 : Nat := 0xffc0070000000000007fe0038000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffffe7fffff0ffc0007ffff3fffff87fe0003fffffffffffc000001fffffffffffe000000ffffffffe00ffffffffffffffffffffffffffffffffff803fffffffffffffffffffffffff004000180d000000c00020000c0680000060000128079be819040400089402cdf40c821a00004a01e6fa06410100022500b37d03208680015be17e2b3018808000adf0bf15980c40400056f84d820c13acac002b7c2fc5660bd6560015be13608304eb2b000adf0bf15982f5958

def w162 : Nat := 0xffe81fa0000ff83ffffad40f500007fc1ffffffffffffffffff0001ffffffffffe1ff8000f4293ea01fff0000007ff49f8000000000003fcfffffffffe000001fffff9802001000000fffe1fffe00fffffffffff0ffff007ffffffffffff0000000000001fc7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w163 : Nat := 0xffe927a01ff0f800007ad493500ff87c00003ffff9fffffc3ff0001ffffcfffffe1ff8000f580060000000000007fe0038000000000003fcfffffffffe00fc01fffff9800011007e00ffffdffff00fffffffffffeffff007ffffffffffff3004020000001fe7ffffffffe0000000040000045204010d00000000c2690200808000128059be819041400009402cdf40c82020000000180d000000400020000002800000600005be17e2b301ca0a000adf08a041002501000525849800c13acac00292c24c00609d6560015be1140820008000002df0bf15980c4040

def w164 : Nat := 0xffe93f0000000000007a149f500fff8000003ffffffffffc3ff0001ffffffffffffff8000f5a81ea0000ff83ffffff40fd00007fc1fffff8fffffffffc000001fffff8000000000000fffe1fffe00fffffffffff0ffff007ffffffffffff3004002000001fe7fffffffff0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w165 : Nat := 0xffe93fa01fff0000007ad49c0000000000003fffffffffffffffffffffffffffffffffffff5a9380000000000007ff49fd00fff8000003fcfffffffffc000001fffff0000000000000ffffdffff00fffffffffffeffff807fffffffffffe0000000000001fe7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w166 : Nat := 0xffe93fa01ffff83ffffff49fd00ffffc1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00fc01ffffffffffff007e00fffffffff00ffffffffffffffffffffffffffffffffffc03fffffffffffffffffffffffff004000184d334813d30020000c2699a409e9800128079becdb04d4c0089402cdf66d827a60004a01e6fb36c13530022500b37d9b609e98015be17e2b381ca8a800adf0bf159c0e54540056f84d820e13aeae002b7c2fc5670bd7570015be13608384ebab800adf0bf159c2f5d5c

def w167 : Nat := 0xfff1c7c010008000007c98e26008004000003ffff9fffffc3ff0001ffffcfffffe1ff8000f900040000000000007fe0038000000000003feffffffffffe0fffffffffd40001ff07fffffff3fffffffffffffffff9ffff007ffffffffffffa807ffc000001ff7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w168 : Nat := 0xfff1d7c01008803f007ff8ebe00804401f803ffffdfffffe3fffc01ffffeffffff1fffe00fffff7fffff8ffff007ffffbfffffc7fff803ffffffffffffe0fffffffffffffffff07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff005050590d0a012aca0028282c868500956500053c17dbea994e86800a9e0aedf54ca75b40014f05f6faa653a1a002a782bb7d5329d6d0015be17f3ffd38cdcc00adf0bf9ffe9c66e60056f84dc73f5bbfff002b7c2fe7ffafdfff8015be1371cfd6efffc00adf0bf9ffebf7ffe

def w169 : Nat := 0xfffe07ffe000ffc0007fff03fff0007fe0003f8001c000000000001c00000000000000000fe00070000000000007000000000000000003fff81fff8003ff0001fffc0fffc001ff8000fe00070000000000007000000000000000003f8001c000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w170 : Nat := 0xfffe07ffe000ffc0007fff03fff0007fe0003ffff9fffffc3ff0001ffffcfffffe1ff8000fe00070000000000007fe0038000000000003ffffffffffffff0001ffffffffc001ff8000fffe1fffe00fffffffffff0ffff007ffffffffffffc000000000001fc7ffffffffe0000000040000001000000c00000000c0600000000000128059be819040400009402cdf40c82020000000180c000000000020000000800000600005be17e2b3018808000adf008040000000000521849800c13acac00290c24c00609d6560015be0100800000000002df0bf15980c4040

def w171 : Nat := 0xfffe180000000000007f1f0ffff0078000003f8ffe0000000000001fc7ff0000000000000fe3e1fffe00f0000007fff0c0000000000003800000000000000001ff800e000000000000e000000000000000007000000000000000003ff001c000000000001c0000000000000000000521800000000000000090c24c0060110100005be0100800000000002df008040000000000121849800c02202000290c00000000000000000004030000000000000000002000000000000000000000000000000000000000000000000000000400000000000000201800000000

def w172 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff0000000000000fe3fffffffff0000007ffffc0000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007000000000000000003ff001c000000000001c0000000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w173 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff0000000000000ff3fffffffff0000007ffffc0000000000003ffffffffffc3ff0001ffffffffffffff8000ffe93f0000000000007a149c0000000000003ffa07e80003c000001eb503000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w174 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff0000000000000ffffffffffff0000007ffffc0000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007f00000000000000003fff81fff8000000001fffc0000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w175 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff8000000000000fe3fffffffff0000007ffffe0000000000003ffffffffffc3ff0001ffffffffffe1ff8000ffe81f0000000000007a140f5000078000003ffa07c000000000001e8503d40001e00000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w176 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff8000000000000ff3fffffffff0000007ffffe6008000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffe9270000000000007a1493500ff80000003ff001c000000000001eb000c00000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w177 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff8000000000000ff3fffffffff8000007ffffe4008004000003ffffdfffffc3ff0001ffffeffffff1ff8000ffe11700000000000078108a4008040000003ff805e00002200fc01e24029000011007e0000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w178 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff8000000000000ff3fffffffff8000007ffffe6000004000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007a00030000000000003ffa01e800003e00001eb500d400001f0000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w179 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffff8000000000000ff3fffffffff8000007ffffe6008004000003ffffffffffc3ff0001ffffffffffffff8000ffe93f0000000000007a149f500fff8000003ffa07e80003fe0ffffeb503d40001ff07fff00521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w180 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffc000000000000ffbfffffffff0000007fffff500ff80000003ffff9fffffc3ff0001ffffcfffffe1ff8000fff1c70000000000007c18e26008000000003ff001c000000000001f2000800000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w181 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffc000000000000ffbffffffffff800007fffff5000007c00003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007c00020000000000003ffc01f000002000001f2600980000100000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w182 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000fe3fffffffff0000007fffff8000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007f00038000000000003fff81c000000000001fc7c0fffc00000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w183 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000ffffffffffff0000007ffffffff0000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007f00038000000000003ff001c000000000001ff800e00000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w184 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000ffffffffffffffc0007ffffffff0007fe0003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007f00038000000000003fff81fff8003ff0001fffc0fffc001ff800000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w185 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000ffffffffffffffc0007ffffffff8007fe0003ffffffffffc3ff0001ffffffffffffff8000ffe93f0000000000007f149fd00fff8000003fff87fff803ffffffffffc3fffc01fffffff00521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w186 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000ffffffffffffffc0007ffffffffff87fe0003ffffffffffc3ff0001ffffffffffffff8000ffffff0000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffff005218598c0c13acac00290c24c08609d6760005be17e3b3018808000adf00806000001800016f85fefec663030002b7c0b37d03208080015be059be81904040002df0bfdfd8cc60600056f80403000000c0000b7c2fc76603101000148612604304eb3b000a430b31818275958

def w187 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffffffffe000000fe3ffffffffffffffffffffffff007fffffffffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007000038000000000003ff001c000003ff0001c0000fffffe1ff800000525849800c13acac00292c24c02609d6560005be17e2b3018808000adf08f05980c40400016f85f8acc17ac2c002b7c22c10609d656000128059be819040400009402cdf40c820a00040000005000000c00000000c0680000060001000001948180434000000034db40c82020

def w188 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc1f0001fffff2bfc0000f8000fe3fffffffff07c0007ffffcaff00003e0003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000007fc0fff000019ff7fbbfe07ffff001c000001ff03ffc000067fdfeeff81fffffb5fe9904c93ecacfffdaff4c82649f6567fefffffeeb32dfb0b3ffffffcf65996fd959ffbfffffbaccb7ec2cfffffff3d9665bf6567feb69ed9ffc7b14547ff5b4f6cffe3d8a2a3ffe907a07531f8d5d5ffd483dd7efaff6afafffa41e81d4c7e35757ff520f75fbebfdabeb

def w189 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffffcfffffffffe000001fffff9802001000000fe3fffffffff0000007ffffe0000000000003ffffffffffffff0001ffffffffffe1ff8000ffe81fa0000ff83ffffad40f500007fc1ffffffa4fc000000000001e8527d403ffe00000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w190 : Nat := 0xfffe1fffe00fffffffffff0ffff007ffffffffcfffffffffe000001fffff9802001000000ff3fffffffff8000007ffffe6008004000003ffffffffffffff0001ffffffffffffff8000ffe93fa0000ff83ffffad49f500ffffc1ffffffa4fe80003fe0ffffeb527d403ffff07fff00521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w191 : Nat := 0xfffedfffe00fffffffffff6ffff007ffffffff8fffffffffc000001fffff0800000000000fe3fffffffff0000007ffffc2000000000003ffffbfffffdfff03ffffffdfffffefff81ffffc82f200ff77800fff244151007fbbc007ffff20bc803fdde003ffc91054401feef001ff00525849800c13acac00292c24c00609d6560005be17e2b301ca0a000adf08a04100250100016f85f8acc072828002b7c228104009404000128059bec5b045440009402cdf62d822a20040000045314811d10000000c2698a408a880100000114c5204744000000309a629022a2

def w192 : Nat := 0xffff1fffe00fffffffffff8ffff807ffffffffcfffffffffc000001fffff9002010000000ff3fffffffff803f007ffffe400004401f803ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007880020000000000003ff841e004002000001e2420900200100000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w193 : Nat := 0xffff1ffff00fffffffffff8ffff807ffffffffcfffffffffc000001fffff0000000000000ff3fffffffff0000007ffffc0000000000003ffffdfffffe3fffc01ffffeffffff1fffe00ffe1178010080000007890880000000000003ff845e004020000001e2422000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w194 : Nat := 0xffff3fffe00fffffffffff9ffff007ffffffffefffffffffc000001fffffd40001e000000ffbfffffffff0000007fffff5000078000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007c80020000000000003ff001c000000000001f2000800000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w195 : Nat := 0xffff3fffe00fffffffffff9fffffffffffffffefffffffffc000001fffff0000000000000ffbfffffffff0000007ffffc0000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007c80000000000000003ffc71f004000000001f2638000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w196 : Nat := 0xffff3fffe00fffffffffff9fffffffffffffffefffffffffc000001fffffd403ffe000000ffbffffffffff83fffffffff500007fc1ffffffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007c80020000000000003ffc71f004002000001f2638980200100000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w197 : Nat := 0xffff3fffe00fffffffffff9fffffffffffffffefffffffffc000001ffffff403ffe000000fffffffffffffffffffffffffff007fffffffffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007f80038000000000003ffff1fffc003ff0001ffff8fffe001ff800000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w198 : Nat := 0xffff3fffffffffffffffff9ffff007ffffffffeffffffffffe0fffffffffd40001ff07fffffbfffffffff0000007fffff500fff8000003ffff9fffffc3ff0001ffffcfffffe1ff8000fff1c7c010008000007c98e26008004000003ff001c000000000001f2000800000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w199 : Nat := 0xffff3fffffffffffffffff9ffff007fffffffffffffffffffffffffffffffffc01fffffffffbfffffffff0000007fffffd00fff8000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffffc7fff000ffc0007fffe3fff8007fe0003ff001c000000000001fe000e00000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w200 : Nat := 0xffff3fffffffffffffffff9fffffffffffffffea4fe807fffe0ffffeb527d403ffff07fffffa93fa01ffff83ffffad49f500ffffc1ffffffff5fffc023fffc01ffffafffe011fffe00ff31d7c01008803f007c98ea600804401f803fcc75f00402200fc01f263a9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w201 : Nat := 0xffff3fffffffffffffffff9fffffffffffffffeffffffffffe0fffffffffd403ffff07fffffbffffffffff83fffffffff500ffffc1ffffffff9fffffc3ff0001ffffcfffffe1ff8000fff1c7c010008000007c98e26008004000003ffc71f004002000001f2638980200100000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w202 : Nat := 0xffff3fffffffffffffffff9fffffffffffffffeffffffffffe0fffffffffd403ffff07fffffbffffffffff83fffffffff500ffffc1ffffffffdfffffe3fffc01ffffeffffff1fffe00fff1d7c01008803f007c98ea600804401f803ffc75f00402200fc01f263a9802011007e0000521849c53f5bbfff00290c24e29faddfff8005be17f3ffd38cdcc00adf0088e669026a60016f85fcfff4e3373002b7c022399a409a980053c15dbea994e8680029e0aedf54ca743400505041010a012aca0008282c8605009505001414104042804ab280020a0b21814025414

def w203 : Nat := 0xffffc7fff000ffc0007fffe3fff8007fe0003fc001c000000000001c00000000000000000ff00070000000000007000000000000000003fff87fff803ffffffffffc3fffc01ffffffffe293fa01fff0000007ad49c0000000000003f8a4fe807ffc000001eb5270000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w204 : Nat := 0xffffd7fff008ffff007fffebfff8047fff803fcc75f00402200fc01f263a9802011007e00ff31d7c01008803f007c98ea600804401f803fffcfffffffffffffffffe7fffffffffffffffa93fa01ffff83ffffad49f500ffffc1fffffea4fe807fffe0ffffeb527d403ffff07fff00105041000a012a0a000828208005009505000414104002804a8280020a082001402541400105041000a012a0a00082820800500950500000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6

def w205 : Nat := 0xffffdfffe00fffffffffffeffff007ffffffffcfffffffffc000001fffff9800010000000ff3fffffffff0000007ffffe6000040000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007ac0030000000000003ff001c000000000001eb000c00000000000000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc062020002b7c228104001000000128059be819040400009402cdf40c820200040000005000000c00000000c06800000000010000001400000300000000301a00000000

def w206 : Nat := 0xffffdfffe00fffffffffffeffff807ffffffffcfffffffffc000001fffff0000000000000ff3fffffffff0000007ffffc0000000000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007ac0000000000000003ffa49e807fc0000001eb524000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w207 : Nat := 0xffffdfffe00fffffffffffeffff807ffffffffcfffffffffc000001fffff9802010000000ff3fffffffff803f007ffffe600004401f803ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007ac0030000000000003ffa49e807fc3e00001eb524d403fe1f0000000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w208 : Nat := 0xffffdfffe00fffffffffffeffff807ffffffffcfffffffffc000001fffff9802010000000ff3fffffffff803f007ffffe600804401f803ffffffffffc3ff0001ffffffffffffff8000ffe93f0000000000007ad49f500fff8000003ffa4fe807fffe0ffffeb527d403ffff07fff00525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w209 : Nat := 0xffffdfffe00fffffffffffeffff807ffffffffcfffffffffc000001ffffff802010000000ffffffffffffffff007ffffffff0047fff803ffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007fc0038000000000003fffc9fffffc3ff0001fffe4fffffe1ff800000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w210 : Nat := 0xffffdfffe00fffffffffffeffff807ffffffffcfffffffffe000001fffff9802011000000ff3fffffffff803f007ffffe600004401f803ffffffffffffff0001ffffffffffe1ff8000ffe81fa0000ff83ffffad40f500007fc1ffffffa4fe807fc3e00001eb527d403ffff0000000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w211 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffca4fe807ffc000001eb5270000000000000ff293fa01fff0000007ad49c0000000000003ffff7fffc03fffffffffffbfffe01fffffffff293fa01fff0000007ad49c0000000000003fca4fe807ffc000001eb5270000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def w212 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffcfffffffffc000001fffff0000000000000ff3fffffffff0000007ffffc0000000000003ffffffffffffffffffffffffffffffffffffffe93fa01fff0000007ad49c0000000000003ffa4fe807ffc000001eb527000000000000000521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w213 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffcfffffffffc000001fffff8000000000000ff3fffffffff8000007ffffe6008004000003ffffffffffffffffffffffffffffffffffffffe93fa01fff0000007ad49f500fff8000003ffa4fe807fffe0ffffeb527d40001ff07fff00521849800c13acac00290c24c00609d6560005be17e2b3018808000adf00804000000000016f85f8acc062020002b7c020100000000000128059be819040400009402cdf40c820200040000001000000c00000000c06000000000010000000400000300000000301800000000

def w214 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffcfffffffffc000001fffff9802010000000ff3fffffffff803f007ffffe600004401f803ffffffffffffffffffffffffffffffffffffffe93fa01fff0000007ad49f0000000000003ffa4fe807fffe00001eb527d403fe1f0000000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w215 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffcfffffffffe00fc01fffff9802011007e00ff3fffffffff803f007ffffe600804401f803ffff9fffffc3ff0001ffffcfffffe1ff8000ffe927a01ff0f800007ad493500ff87c00003ffa49e807fc3e00001eb524d403fe1f0000000525849800c13acac00292c24c00609d6560005be17e2b301ca0a000adf08a04100250100016f85f8acc072828002b7c228104009404000128059be819041400009402cdf40c820a00040000045204010d00000000c26902008280010000011481004340000000309a408020a0

def w216 : Nat := 0xffffdffff00fffffffffffeffff807ffffffffcfffffffffe00fc01fffff9802011007e00ff3fffffffff803f007ffffe600804401f803ffffffffffffffffffffffffffffffffffffffe93fa01ffff83ffffad49f500ffffc1ffffffa4fe807fffe0ffffeb527d403ffff07fff00525849800e13aeae00292c24c00709d7570005be17e2b381ca8a800adf08a04140254140016f85f8ace072a2a002b7c228105009505000128059becdb04d4c0009402cdf66d826a60040000045334813d30000000c2699a409a980100000114cd204f4c000000309a669026a6

def w217 : Nat := 0xffffe00000000000007f1ff3fffff80000003ff0000000000000001c00000000000000000ffc0070000000000007000000000000000003800000000000000001ff800e000000000000e000000000000000007fe0000000000000003f8ff9fffffc0000001ffffc00000000000000004a00402000000000002500b0540020000001000000000000000000000030100000000000400000000000008000000004000000000000000002000000000000080000000000001000000001808000000000020000000000000000001280582a00100000000940080400000000

def w218 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001c00000000000000000ffc0070000000000007000000000000000003fff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007ffffc0000000000003f8fffffffffc000001fffff00000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w219 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001c0000e000000000000ffc007000000ffc000700003fffff87fe0003fff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007fffffffffff8000003f8ffffffffffffffffffffffffc01fffffff0004a0166fa06410100002500b37d03208280010000001400000300000000301a000001800040000065206010d00000000d36d032080800149612600304eb2b000a4b09300982759580016f85f8acc062020002b7c23c1660310100005be17e2b305eb0b000adf08b0418275958

def w220 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001eb000c000000000000ffe927a01ff0f800007ad493500ff87c00003ffff7fff803fffffffffffbfffe01fffffffff3fffffffff0000007ffffe6008040000003fcfffffffffe00fc01fffff9800011007e000004a0166fa06410100002500b37d03208280010000001400000300000000301a000000800040000045204010d00000000c269020080800149612600304eb2b000a4b09300182759580016f85f8acc062020002b7c2281040010000005be17e2b301ca0a000adf08a0410025010

def w221 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001f20008000000000000fff1c7c010008000007c98e26008004000003fffcffff803ffffffffffe7fffffffffffffffbfffffffff0000007fffff500fff8000003feffffffffffe0fffffffffd40001ff07fff0004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w222 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001fc000e000000000000fffe07ffe000ffc0007fff03fff0007fe0003fff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007fffff8000000000003ffffffffffffff0001ffffffffc001ff80000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w223 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001fe000e000000000000ffffc7fff000ffc0007fffe3fff8007fe0003fffcffff803ffffffffffe7fffffffffffffffbfffffffff0000007fffffd00fff8000003ffffffffffffffffffffffffffc01fffffff0004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w224 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001ff800e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffffffff803fffffffffffffffffffffffffffffffffffff0000007fffffffffff8000003ffffffffffffffffffffffffffc01fffffff0004a01e6fa06410100022500b37d03208680010000603400000300008000301a000001800044a0166fa06410d00002500f37d03208080015be13608304eb2b000adf0bf15982f59580056f85f8acc062020002b7c2fc5660310100015be17e2b305eb2b000adf09b0418275958

def w225 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000003ffffffc0000fffffffffffffffc007000000fffffff00003ffffffffffffffff87fff803ffffffffffc3fffc01ffffffffe3fffffffffffffffffffffffffffffffffff8ffffffffffffffffffffffffffffffffffffade7b67ff3ec5353ffd6f3db3ff9f629a9fffa41e81d4cfe77f7fff520ff7fbffffffffffe907a07533f9dfdfffd483fdfefffffffffffed7fa6417e6fbfbffff6bfd320bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffbfffffcffffffffcfe7ffffffff

def w226 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ffc71f004002000001f26389802001000000ffc0070000000000007c80020000000000003fffcfffffffffffffffffe7fffc01fffffffffbffffffffff83fffffffff500007fc1fffffefffffffffc000001fffffd403ffe0000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w227 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003fff81fff8003ff0001fffc0fffc001ff8000ffc0070000000000007f00038000000000003fff87fff803ffffffffffc3fffc01fffffffffffffffffffffc0007ffffffff0007fe0003f8fffffffffc000001fffffe0000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w228 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ffff1fffc003ff0001ffff8fffe001ff8000ffc0070000000000007f80038000000000003fffcfffffffffffffffffe7fffc01ffffffffffffffffffffffffffffffffff007ffffffffefffffffffc000001ffffff403ffe0000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w229 : Nat := 0xffffe7fffff0ffc0007ffff3fffff87fe0003ffff9fffffc3ff0001ffffcfffffe1ff8000ffffe7fffff0ffc0007ffff3fffff87fe0003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0044a01e6fa06410d00022500f37d0320868001128079be819043400089403cdf40c821a00044a01e6fa06410d00022500f37d03208680015be17e2b305eb2b000adf0bf15982f59580056f85f8acc17acac002b7c2fc5660bd6560015be17e2b305eb2b000adf0bf15982f5958

def w230 : Nat := 0xfffff7fffff8ffff007ffffbfffffc7fff803ffc75f00402200fc01f263a9802011007e00fff1d7c01008803f007c98ea600804401f803fffcfffffffffffffffffe7fffffffffffffffbffffffffff83fffffffff500ffffc1fffffeffffffffffe0fffffffffd403ffff07fff0014f0576faa653a1a000a782bb7d5329d0d001414104042804ab280020a0b2181402541400505041010a012aca0008282c860500950500148612714fd6efffc00a430938a7eb77ffe0016f85fcfff4e3373002b7c022399a409a98005be17f3ffd38cdcc00adf0088e669026a6

def w231 : Nat := 0xfffff80000000000007f1fffffffff8000003ffffe0000000000001fc7ffffffffe000000fffe1fffe00fffffffffff0ffff007fffffff800000000000000001ff800e000000000000e000000000000000007fe0038000000000003ffff9fffffc3ff0001ffffcfffffe1ff80000056f8040200000000000b7c2fc5660310100015be0100800000000002df0bf15980c404000521849800c13acac00290c24c00609d6560000000603000000000008000000200000180000000180c00000000002000000080000060000128059be819040400009402cdf40c82020

def w232 : Nat := 0xfffff80000000000007f1fffffffff8000003ffffe0000000000001fffffffffffe000000fffe1fffe00fffffffffff0ffff007ffffffff8ffe0000000000001fffffe000000000000fffe180000000000007fff0ffff0078000003ffffffffffc3ff0001ffffffffffffff80000056f8040200000000000b7c2fc5660310100015be0503800000000002df0bf17980c4040005218598c0c13acac00290c24c08609d6560005be070380000000000adf0080600000180005218180c0000000000290c24c0860110700015ae059be81904040002d70bfdf58cc6060

def w233 : Nat := 0xfffff80000000000007f9fffffffff8000003ffffe0000000000001fe7ffffffffe000000ffffdffff00fffffffffffeffff807fffffffd6a4e0000000000001ffd27f403ffe000000f5a9380000000000007ff49fd00fff8000003ffffffffffffffffffffffffffffffffffff0056f8040200000000000b7c2fc5660310100015be0100800000000002df0bf15980c404000521849800c13acac00290c24c00609d6560000000603000000000008000000200000180000000180c00000000002000000080000060000128059be819040400009402cdf40c82020

def w234 : Nat := 0xfffff80000000000007fffffffffff8000003ffffe0000000000001fffffffffffe000000fffffffffffffffffffffffffffffffffffffffffe0000000000001fffffffffffe000000fffff80000000000007fffffffffff8000003ffffffffffffffffffffffffffffffffffff0056f81c0e00000000002b7c2fc5e60310700015be070380000000000adf0bf17980c41c00056b85fefac77bcbc002b5c2ff7d63bde5e0015be070380000000000adf0bf17980c41c00056f81c0e00000000002b7c2fc5e60310700015ae17fbeb1def2f000ad70bfdf58ef7978

def w235 : Nat := 0xfffff8001ff00000007f1fffffffff8000003ffffe0000003fffffffc7ffffffffffffffffffe1fffe00fffffffffff0ffffffffffffff80006000003c00ffffff803e00001e007fffe03ff8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb67ff3ec5353ffdffffffffff739b9ffffffe91dccfe77f7fff7ffffffffffffffffffb1fe9f53ffbfffffffd8ffdfefffffffffffed7fe6717e6fbfbffff6bfd322bf37dfdfffbffffffeffffff3ffffffff3f9ffffffffffefffffffffffffcffffffffefffffffffff

def w236 : Nat := 0xfffff95fe00007c0007f3fffffffff83e0003ffffe57f80001f0001fcfffffffffe0f8000fffedfffe00fffffffffff6ffff007fffffff9b38acffbfddff03ffff9c5e7fdfeeff81ffe6ce2b3feff77fc0ffffe7179ff7fbbfe07ffffffbfffffdfff03ffffffdfffffefff81ffffffffffbaccb7ecacffffffffdd665bf6567fffffffeeb32dfb2b3ffffffff75996fd959ffffffffbaccb7ecacffffffffdd665bf6567ffbebefbffd7fb57d7ffdf5f7dffebfdabebffefafbefff5fed5f5fff7d7df7ffaff6afafffbebefbffd7fb57d7ffdf5f7dffebfdabeb

def w237 : Nat := 0xfffffcc01008803f007f9fffffffffc01f803fffff300402200fc01fe7fffffffff007e00ffffdffff00fffffffffffeffff807fffffffd6a4fa807fffe0ffffffd27f403ffff07ffff5a93ea01ffff83ffffff49fd00ffffc1ffffffffffffffffffffffffffffffffffffffff0056f845020a012a0a000b7c2fc5670395150015be114082804a828002df0bf159c0e545400525849800e13aeae00292c24c00709d75700000006134cd204d4c008000008a669027a6000000184d33481353002000002299a409e9800128059becdb04d4c0009402cdf66d826a6

def w238 : Nat := 0xfffffcc01008803f007fffffffffffc01f803fffff300402200fc01ffffffffffff007e00ffffffffffffffffffffffffffffffffffffffffffa807fffe0fffffffffffffffff07ffffffffea01ffff83ffffffffffffffffc1ffffffffffffffffffffffffffffffffffffffff0056f85d0e0a012a0a002b7c2fc5e70395750015be174382804a82800adf0bf179c0e55d40056f85fefae77bebe002b7c2ff7d73bdf5f0015be0713ccd204d4c00adf0bf9ffe9c67e60056f81c4f33481353002b7c2fe7ffa719f98015ae17fbefdfefffc00ad70bfdf7eff7ffe

def w239 : Nat := 0xfffffea01ffff83fffffdffffffffffc1fffffffffa807fffe0ffffff7ffffffffff07fffffff3fffffffffffffffff9ffffffffffffffe4c75300402200fc01ffe3af802011007e00f931d4c01008803f007ff8ebe00804401f803ffffdfffffe3fffc01ffffeffffff1fffe000056f8044733481353000b7c2fe7ffa719b98015be0111ccd204d4c002df0bf9ffe9c66e600521849c53f5bbfff00290c24e29faddfff800414164302804a82800a0a0820214025594001050590c0a012a0a00282820808500956500053c15dbea994e8680029e0aedf54ca7434

def w240 : Nat := 0xffffff0000000000007f1fffffffff8000003fffffc000000000001fc7ffffffffe000000fffe1fffe00fffffffffff0ffff007ffffffff8f87fff803c000001fffc3e000000000000fe3e1fffe00f0000007fff0f8000000000003ffffffffffc3ff0001ffffffffffe1ff80000056f8040300000000000b7c2fc7660310100015be0100c00000000002df0bf1d980c404000521849800c13acac00290c24c00609d656000486166303008808000a430000200000180001218598c0c02202000290c0000800000600005be059be81904040002df02cdf40c82020

def w241 : Nat := 0xffffff0000000000007f1fffffffff8000003ffffffffffc3ff0001ffffffffffffff8000fffe1fffe00fffffffffff0ffff007ffffffff8fffffffffc000001fffffe000000000000fffe1fffe00fffffffffff0ffff007fffffffffffffffffc3ff0001ffffffffffffff80000056f80403000000c0000b7c2fc7660310100015be059be81904040002df0bfdfd8cc6060005218598c0c13acac00290c24c08609d6760005be17e3b3018808000adf0080600000180005218598c0c13acac00290c24c08609d6760015be059be81904040002df0bfdfd8cc6060

def w242 : Nat := 0xffffff0000000000007fffffffffff8000003ffffffffffc3ff0001ffffffffffffff8000ffffffffffffffffffffffffffffffffffffffffffffffffc000001fffffffffffe000000ffffffffe00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0056f81c0f000000c0002b7c2fc7e60310700015be079be8190404000adf0bfdfd8cc61e00056b85fefac77bcbc002b5c2ff7d63bde7e0015be17e3b3018808000adf0bf17980c41c00056f85d8e0c13acac002b7c2fc5e60bd6760015be17fbeb1def2f000adf0bfdfd8ef7978

def w243 : Nat := 0xffffffc01008803f007f9fffffffffc01f803ffffffffffe3fffc01fffffffffffffffe00ffffdffff00fffffffffffeffff807ffffffffeffffffffffe0ffffffffff403ffff07fffffff3fffffffffffffffff9ffffffffffffffffffffffffffffffffffffffffffffffffff0056f845030a012aca000b7c2fc7670395150015be15dbea994e868002df0bfdfdcce7474005258598c0e13aeae00292c24c08709d7770005be17f3ffd38cdcc00adf0088e669027a600521859cd3f5bbfff00290c24e29faddfff8015be059becdb04d4c002df0bfdffedc66e6

def w244 : Nat := 0xffffffffe00fffffffffffffffffffffffffffefffffffffc000001fffffdc03ffe000000ffbffffffffff83fffffffff700007fc1ffffffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007ec0030000000000003ffe79f807fc3e00001fb73cdc03fe1f0000000525849800c13acac00292c24c00609d6560005be17e2b3018808000adf08a04100040000016f85f8acc072828002b7c228104009404000128059be819040400009402cdf40c820a00040000005000000c00000000c06800000200010000011481004340000000309a40802020

def w245 : Nat := 0xffffffffe00fffffffffffffffffffffffffffffffffffffc000001fffffffffffe000000fffffffffffffffffffffffffff007fffffffffff9fffffc3ff0001ffffcfffffe1ff8000ffc0070000000000007fe0038000000000003ffff9fffffc3ff0001ffffcfffffe1ff80000056f84d820c13acac002b7c2fc5660bd6560015be17e2b3018808000adf0bf15980c40400056f85f8acc17acac002b7c26c10609d656000128079be819040400089402cdf40c821a0004000180d000000c00020000c0680000060001128059be819043400009403cdf40c82020

def w246 : Nat := 0xfffffffffff0ffc0007fffffffffffffe0003ffa4fc000000000001e8527d403ffe000000ffe81fa0000ff83ffffad40f500007fc1fffffff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007ffffe0000000000003fcfffffffffe000001fffff98020010000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w247 : Nat := 0xfffffffffff0ffc0007fffffffffffffe0003fffffc000000000001fc7ffffffffe000000fffe1fffe00fffffffffff0ffff007ffffffffff87fff803ffffffffffc3fffc01ffffffffe3fffffffff0000007fffff8000000000003ffffffffffffff0001ffffffffffe1ff80000056f8166fa0641010000b7c2ff7f63318180015be0100c00000300002df0bf1d980c404000521849810c13acec00290c2cc60609d65600148616630304eb2b000a4309302182759d80016f85f8ecc062020002b7c0201800000600005be17fbfb198c0c000adf02cdf40c82020

def w248 : Nat := 0xfffffffffff0ffc0007fffffffffffffe0003ffffffffffc3ff0001ffffffffffffff8000fffe1fffe00fffffffffff0ffff007fffffffffffffffffffffffffffffffffc01ffffffffffffffffffffffffffffffffff007fffffffffffffffffffff0001ffffffffffffff80000056f8166fa06410d0000b7c2ff7f63318180015be059be81904340002df0bfdfd8cc6060005218598d0c13acec00290c2cc68609d6760015be17e3b305eb2b000adf09b06182759d80056f85f8ecc17acac002b7c26c18609d6760015be17fbfb198c0c000adf0bfdfd8cc6060

def w249 : Nat := 0xffffffffffff0000007fffffffffff8000003ffffffff803fffffffffffffffffffffffffffffffffe00ffffffffffffffffffffffffffff001c000000000001ff800e000000000000ffffe7fffff0ffc0007ffff3fffff87fe0003ffff9fffffc3ff0001ffffcfffffe1ff80000056f85f8acc062020002b7c2fc5660310100015be13608304eb2b000adf0bf15982f59580056f84d820c13acac002b7c2fc5660bd6560010000603400000300008000301a000001800004a01e6fa06410100022500b37d0320868000128079be819040400089402cdf40c821a0

def w250 : Nat := 0xffffffffffffffc0007ffffffff0007fe0003fff87fff803ffffffffffc3fffc01fffffffffffff0000000000007f1fffffffff8000003fff81fff8003ff0001fffc0fffc001ff8000ffffe7fffff0ffc0007ffff3fffff87fe0003f8001c000000000001ff800e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w251 : Nat := 0xffffffffffffffc0007ffffffff8007fe0003fff87fff803ffffffffffc3fffc01fffffffffffff0000000000007f1fffffffff8000003fff87fff803ffffffffffc3fffc01fffffffffffffffffffffc0007ffffffffff87fe0003f8a4fe807ffc000001ffd27e0000000000000016f85f8acc062020002b7c02010000000000148612600304eb2b000a4309300182759580056f8040200000000000b7c2fc56603101000100000004000003000000003018000000000004a0166fa06410100002500b37d03208080000000603000000000008000000200000180

def w252 : Nat := 0xffffffffffffffc0007ffffffffff87fe0003fff87fff803ffffffffffc3fffc01fffffffffe93f0000000000007f149fd00fff8000003fff87fff803ffffffffffc3fffc01fffffffffffffffffffffc0007ffffffff8007fe0003f8fffffffffc000001fffffe0000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w253 : Nat := 0xfffffffffffffffffffffffffff007fffffffffffffffffffffffffffffffffc01fffffffffffffffffff0000007fffffffffff8000003ffff9fffffc3ff0001ffffcfffffe1ff8000ffffe7fffff0ffc0007ffff3fffff87fe0003ff001c000000000001ff800e0000000000000056f85f8acc17acac002b7c26c10609d6560015be17e2b305eb2b000adf09b04182759580056f85f8acc062020002b7c2fc566031010001128059be819043400009403cdf40c820200044a0166fa06410d00002500f37d03208080010000603400000300008000301a00000180

def w254 : Nat := 0xffffffffffffffffffffffffffffffffffffffea4fe807fffe0ffffeb527d403ffff07fffffa93fa01ffff83ffffad49f500ffffc1ffffffff7fffc03fffffffffffbfffe01fffffffff39ffe01fff803f007edcfe600804401f803fce7ff807ffe00fc01fb73f9802011007e00000000004533481353000000002299a409a980000000114cd204d4c000000008a669026a6000000004533481353000000002299a409a9800414104002804a8280020a082001402541400105041000a012a0a000828208005009505000414104002804a8280020a0820014025414

def w255 : Nat := 0xfffffffffffffffffffffffffffffffffffffffa4fe807ffc000001eb5270000000000000ffe93fa01fff0000007ad49c0000000000003ffff7fffc03fffffffffffbfffe01fffffffff3fffffffff0000007ffffc0000000000003fcfffffffffc000001fffff00000000000000004a0166fa06410100002500b37d032080800100000004000003000000003018000000000040000001000000c00000000c060000000000148612600304eb2b000a4309300182759580016f85f8acc062020002b7c0201000000000005be17e2b3018808000adf0080400000000

def w256 : Nat := 0xfffffffffffffffffffffffffffffffffffffffa4fe807fffe0ffffeb527d403ffff07fffffe93fa01ffff83ffffad49f500ffffc1ffffffff7fffc03fffffffffffbfffe01fffffffff3fffffffff803f007ffffe600804401f803fcfffffffffe00fc01fffff9802011007e000004a0166fb36c13530002500b37d9b609a980100000114cd204f4c000000309a669026a60040000045334813d30000000c2699a409a980149612600384ebab800a4b093001c275d5c0016f85f8ace072a2a002b7c2281050095050005be17e2b381ca8a800adf08a0414025414

def w257 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffc000001fffff0000000000000ffffffffffff0000007ffffc0000000000003ffffffffffffffffffffffffffffffffffffffffffffffff0000007ffffc0000000000003fffffffffffc000001fffff00000000000000056b85fefac77bcbc002b5c2ff7d63bde5e0015be17e2f3018838000adf0381c000000000056f85f8bcc0620e0002b7c0e07000000000015ae17fbeb1def2f000ad70bfdf58ef79780056f85f8bcc0620e0002b7c0e07000000000015be17e2f3018838000adf0381c00000000

def w258 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 224 then (if i < 112 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then [] else (if i < 2 then [] else [])) else (if i < 5 then (if i < 4 then [] else []) else (if i < 6 then [] else []))) else (if i < 10 then (if i < 8 then [w65, w112, w142, w167, w172, w200, w231] else (if i < 9 then [w65, w112, w130, w142, w155, w197, w218] else [w65, w77, w97, w142, w155, w196, w218])) else (if i < 12 then (if i < 11 then [w65, w77, w112, w142, w155, w211, w231] else [w65, w112, w155, w172, w231, w251, w254]) else (if i < 13 then [w65, w112, w142, w151, w172, w228, w231] else [w65, w112, w142, w155, w212, w231, w254])))) else (if i < 21 then (if i < 17 then (if i < 15 then [w65, w77, w112, w155, w199, w231, w252] else (if i < 16 then [w65, w77, w112, w142, w155, w172, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w231])) else (if i < 19 then (if i < 18 then [w39, w65, w112, w142, w155, w172, w218, w231] else [w22, w25, w65, w77, w112, w142, w218, w231]) else (if i < 20 then [w22, w26, w65, w77, w112, w155, w218, w231] else [w22, w43, w77, w112, w142, w155, w218, w231]))) else (if i < 24 then (if i < 22 then [w22, w39, w65, w112, w142, w155, w218, w231] else (if i < 23 then [w6, w22, w65, w77, w112, w142, w155, w231] else [w65, w77, w112, w142, w155, w184, w218, w231])) else (if i < 26 then (if i < 25 then [w65, w112, w130, w142, w155, w172, w218, w231] else [w39, w43, w112, w142, w155, w172, w218, w231]) else (if i < 27 then [w65, w77, w97, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w207, w218, w231]))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then [w65, w77, w112, w142, w155, w179, w218, w231] else (if i < 30 then [w65, w77, w112, w142, w155, w196, w218, w231] else [w65, w81, w112, w142, w155, w172, w218, w231])) else (if i < 33 then (if i < 32 then [w65, w77, w112, w142, w155, w212, w218, w231] else [w22, w26, w31, w65, w77, w155, w218, w231]) else (if i < 34 then [w6, w22, w26, w65, w77, w112, w155, w231] else [w22, w25, w39, w65, w112, w142, w218, w231]))) else (if i < 38 then (if i < 36 then [w22, w65, w77, w112, w144, w155, w218, w231] else (if i < 37 then [w22, w65, w77, w112, w142, w158, w218, w231] else [w22, w65, w77, w112, w142, w155, w222, w231])) else (if i < 40 then (if i < 39 then [w22, w77, w112, w137, w142, w155, w218, w231] else [w22, w65, w112, w130, w142, w155, w218, w231]) else (if i < 41 then [w65, w77, w112, w116, w142, w155, w218, w231] else [w22, w26, w43, w77, w112, w155, w218, w231])))) else (if i < 49 then (if i < 45 then (if i < 43 then [w22, w26, w39, w65, w112, w155, w218, w231] else (if i < 44 then [w5, w22, w26, w65, w77, w112, w155, w218] else [w22, w39, w43, w112, w142, w155, w218, w231])) else (if i < 47 then (if i < 46 then [w6, w22, w39, w65, w112, w142, w155, w231] else [w22, w65, w77, w112, w143, w155, w218, w231]) else (if i < 48 then [w22, w65, w77, w112, w142, w157, w218, w231] else [w22, w65, w81, w112, w142, w155, w218, w231]))) else (if i < 52 then (if i < 50 then [w22, w65, w77, w112, w146, w155, w218, w231] else (if i < 51 then [w22, w65, w77, w112, w142, w155, w221, w231] else [w52, w65, w77, w112, w142, w155, w218, w231])) else (if i < 54 then (if i < 53 then [w22, w65, w77, w97, w142, w155, w218, w231] else [w22, w65, w77, w112, w147, w155, w218, w231]) else (if i < 55 then [w65, w67, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w167, w218, w231])))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then [w22, w65, w77, w112, w148, w155, w218, w231] else (if i < 58 then [w22, w65, w87, w112, w142, w155, w218, w231] else [w50, w65, w77, w112, w142, w155, w172, w218])) else (if i < 61 then (if i < 60 then [w22, w65, w77, w112, w124, w142, w155, w218] else [w22, w65, w77, w112, w142, w156, w218, w231]) else (if i < 62 then [w22, w65, w77, w112, w142, w155, w220, w231] else [w22, w77, w86, w112, w142, w155, w218, w231]))) else (if i < 66 then (if i < 64 then [w22, w65, w77, w112, w142, w165, w218, w231] else (if i < 65 then [w22, w65, w77, w112, w152, w155, w218, w231] else [w22, w65, w77, w112, w142, w164, w218, w231])) else (if i < 68 then (if i < 67 then [w22, w65, w77, w112, w142, w155, w231, w246] else [w51, w65, w77, w112, w142, w155, w172, w231]) else (if i < 69 then [w21, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w163, w218, w231])))) else (if i < 77 then (if i < 73 then (if i < 71 then [w22, w65, w77, w112, w115, w142, w155, w218] else (if i < 72 then [w22, w65, w77, w112, w142, w155, w219, w231] else [w22, w65, w77, w112, w155, w218, w231, w250])) else (if i < 75 then (if i < 74 then [w22, w65, w77, w112, w142, w170, w218, w231] else [w22, w77, w112, w142, w155, w204, w218, w231]) else (if i < 76 then [w22, w65, w112, w142, w155, w200, w218, w231] else [w22, w65, w77, w112, w142, w155, w203, w231]))) else (if i < 80 then (if i < 78 then [w22, w65, w77, w112, w149, w155, w218, w231] else (if i < 79 then [w22, w65, w77, w112, w142, w162, w218, w231] else [w22, w65, w77, w112, w153, w155, w218, w231])) else (if i < 82 then (if i < 81 then [w22, w65, w77, w112, w142, w155, w231, w255] else [w22, w77, w85, w112, w142, w155, w218, w231]) else (if i < 83 then [w65, w77, w112, w115, w142, w155, w172, w218] else [w65, w77, w112, w142, w155, w187, w218, w231]))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then [w65, w77, w112, w155, w172, w227, w231, w253] else (if i < 86 then [w65, w112, w142, w155, w172, w200, w224, w231] else [w65, w112, w130, w142, w155, w172, w218, w249])) else (if i < 89 then (if i < 88 then [w65, w77, w112, w142, w155, w190, w218, w231] else [w65, w77, w112, w142, w155, w213, w218, w231]) else (if i < 90 then [w65, w84, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w201, w218, w231]))) else (if i < 94 then (if i < 92 then [w65, w77, w97, w142, w155, w172, w218, w249] else (if i < 93 then [w65, w77, w110, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w215, w218, w231])) else (if i < 96 then (if i < 95 then [w59, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w175, w218, w231]) else (if i < 97 then [w65, w77, w112, w142, w155, w173, w218, w231] else [w65, w78, w112, w142, w155, w172, w218, w231])))) else (if i < 105 then (if i < 101 then (if i < 99 then [w65, w77, w112, w142, w155, w194, w218, w231] else (if i < 100 then [w65, w77, w112, w142, w155, w205, w218, w231] else [w65, w77, w112, w142, w155, w182, w218, w231])) else (if i < 103 then (if i < 102 then [w65, w77, w112, w142, w155, w174, w218, w231] else [w65, w77, w112, w142, w155, w183, w218, w231]) else (if i < 104 then [w65, w112, w129, w142, w155, w172, w218, w231] else [w65, w112, w127, w142, w155, w172, w218, w231]))) else (if i < 108 then (if i < 106 then [w65, w112, w126, w142, w155, w172, w218, w231] else (if i < 107 then [w65, w112, w142, w155, w172, w200, w231, w257] else [w65, w77, w112, w142, w155, w208, w218, w231])) else (if i < 110 then (if i < 109 then [w2, w65, w77, w142, w155, w172, w218, w231] else [w15, w77, w112, w142, w155, w172, w218, w231]) else (if i < 111 then [w18, w65, w77, w112, w142, w155, w218, w231] else [w39, w65, w112, w142, w155, w172, w222, w231]))))))) else (if i < 168 then (if i < 140 then (if i < 126 then (if i < 119 then (if i < 115 then (if i < 113 then [w39, w65, w112, w142, w155, w184, w218, w231] else (if i < 114 then [w65, w77, w112, w144, w155, w172, w222, w231] else [w65, w77, w112, w144, w155, w184, w218, w231])) else (if i < 117 then (if i < 116 then [w65, w77, w112, w142, w155, w184, w222, w231] else [w65, w112, w130, w142, w155, w172, w222, w231]) else (if i < 118 then [w65, w112, w130, w142, w155, w184, w218, w231] else [w39, w112, w137, w142, w155, w172, w218, w231]))) else (if i < 122 then (if i < 120 then [w65, w112, w119, w142, w155, w172, w218, w231] else (if i < 121 then [w49, w65, w130, w142, w155, w172, w218, w231] else [w11, w65, w112, w142, w155, w172, w218, w231])) else (if i < 124 then (if i < 123 then [w65, w112, w124, w130, w142, w155, w172, w218] else [w112, w130, w137, w142, w155, w172, w218, w231]) else (if i < 125 then [w65, w77, w112, w142, w155, w178, w218, w231] else [w65, w77, w112, w142, w155, w181, w218, w231])))) else (if i < 133 then (if i < 129 then (if i < 127 then [w65, w79, w112, w142, w155, w172, w218, w231] else (if i < 128 then [w65, w77, w95, w112, w142, w155, w196, w218] else [w65, w77, w98, w142, w155, w172, w218, w231])) else (if i < 131 then (if i < 130 then [w65, w77, w112, w142, w155, w210, w218, w231] else [w65, w77, w112, w142, w155, w214, w218, w231]) else (if i < 132 then [w65, w77, w112, w142, w155, w176, w218, w231] else [w65, w77, w112, w142, w155, w195, w218, w231]))) else (if i < 136 then (if i < 134 then [w65, w80, w112, w142, w155, w172, w218, w231] else (if i < 135 then [w65, w77, w112, w142, w155, w206, w218, w231] else [w65, w77, w112, w142, w155, w180, w218, w231])) else (if i < 138 then (if i < 137 then [w39, w65, w97, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w207, w218, w231]) else (if i < 139 then [w65, w70, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w179, w218, w231]))))) else (if i < 154 then (if i < 147 then (if i < 143 then (if i < 141 then [w39, w65, w112, w142, w155, w172, w221, w231] else (if i < 142 then [w39, w65, w112, w142, w155, w212, w218, w231] else [w39, w65, w69, w142, w155, w172, w218, w231])) else (if i < 145 then (if i < 144 then [w39, w65, w112, w142, w155, w191, w218, w231] else [w39, w86, w112, w142, w155, w172, w218, w231]) else (if i < 146 then [w39, w65, w112, w142, w155, w196, w218, w231] else [w39, w65, w112, w142, w155, w172, w231, w255]))) else (if i < 150 then (if i < 148 then [w39, w65, w112, w142, w155, w172, w231, w246] else (if i < 149 then [w39, w65, w112, w124, w142, w155, w172, w218] else [w39, w65, w112, w142, w155, w172, w220, w231])) else (if i < 152 then (if i < 151 then [w65, w69, w77, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w191, w218, w231]) else (if i < 153 then [w49, w65, w77, w124, w142, w155, w172, w218] else [w65, w77, w112, w148, w155, w172, w231, w256])))) else (if i < 161 then (if i < 157 then (if i < 155 then [w65, w77, w112, w150, w155, w198, w218, w231] else (if i < 156 then [w65, w77, w112, w142, w155, w216, w231, w255] else [w65, w77, w100, w142, w155, w172, w218, w231])) else (if i < 159 then (if i < 158 then [w65, w77, w112, w149, w155, w216, w218, w231] else [w65, w77, w112, w142, w155, w188, w218, w231]) else (if i < 160 then [w65, w97, w131, w142, w155, w172, w218, w231] else [w23, w65, w77, w112, w142, w155, w218, w231]))) else (if i < 164 then (if i < 162 then [w65, w77, w97, w142, w155, w185, w218, w231] else (if i < 163 then [w65, w77, w97, w142, w155, w172, w223, w231] else [w65, w77, w97, w142, w155, w172, w218, w233])) else (if i < 166 then (if i < 165 then [w65, w112, w131, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w185, w218, w231]) else (if i < 167 then [w65, w77, w112, w142, w155, w197, w218, w231] else [w34, w65, w77, w142, w155, w172, w218, w231])))))) else (if i < 196 then (if i < 182 then (if i < 175 then (if i < 171 then (if i < 169 then [w9, w65, w77, w112, w142, w155, w218, w231] else (if i < 170 then [w65, w77, w112, w147, w155, w207, w218, w231] else [w65, w77, w112, w142, w155, w177, w218, w231])) else (if i < 173 then (if i < 172 then [w65, w77, w112, w142, w155, w192, w218, w231] else [w65, w77, w112, w142, w155, w193, w218, w231]) else (if i < 174 then [w65, w77, w112, w153, w155, w202, w218, w231] else [w65, w112, w142, w155, w172, w202, w231, w255]))) else (if i < 178 then (if i < 176 then [w65, w77, w112, w142, w155, w209, w218, w231] else (if i < 177 then [w33, w65, w77, w142, w155, w172, w218, w231] else [w41, w65, w77, w112, w142, w155, w172, w218])) else (if i < 180 then (if i < 179 then [w30, w77, w112, w142, w155, w172, w218, w231] else [w35, w65, w77, w142, w155, w172, w218, w231]) else (if i < 181 then [w19, w65, w77, w112, w142, w155, w218, w231] else [w65, w77, w112, w143, w155, w172, w221, w231])))) else (if i < 189 then (if i < 185 then (if i < 183 then [w65, w77, w112, w143, w155, w179, w218, w231] else (if i < 184 then [w65, w81, w112, w142, w155, w179, w218, w231] else [w65, w77, w112, w146, w155, w189, w218, w231])) else (if i < 187 then (if i < 186 then [w65, w77, w112, w142, w155, w179, w221, w231] else [w12, w65, w77, w112, w142, w155, w218, w231]) else (if i < 188 then [w65, w77, w112, w152, w155, w196, w218, w231] else [w65, w81, w112, w142, w155, w172, w221, w231]))) else (if i < 192 then (if i < 190 then [w65, w77, w112, w146, w155, w172, w226, w231] else (if i < 191 then [w37, w77, w112, w142, w155, w172, w218, w231] else [w65, w81, w112, w142, w155, w172, w218, w233])) else (if i < 194 then (if i < 193 then [w8, w65, w77, w112, w142, w155, w218, w231] else [w65, w77, w112, w142, w155, w218, w231, w244]) else (if i < 195 then [w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w112, w142, w155, w172, w218, w231]))))) else (if i < 210 then (if i < 203 then (if i < 199 then (if i < 197 then [w22, w65, w77, w112, w142, w155, w218, w231] else (if i < 198 then [w22, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w161, w172, w218, w231])) else (if i < 201 then (if i < 200 then [w65, w77, w92, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w172, w218, w231, w234]) else (if i < 202 then [w65, w77, w95, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w172, w218, w231, w241]))) else (if i < 206 then (if i < 204 then [w65, w77, w101, w112, w142, w155, w172, w218, w231] else (if i < 205 then [w65, w65, w77, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w172, w218, w231])) else (if i < 208 then (if i < 207 then [w39, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w132, w142, w155, w172, w218, w231]) else (if i < 209 then [w60, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w139, w142, w155, w172, w218, w231])))) else (if i < 217 then (if i < 213 then (if i < 211 then [w49, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 212 then [w65, w77, w88, w112, w142, w155, w172, w218, w231] else [w53, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 215 then (if i < 214 then [w22, w65, w77, w112, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w231, w231]) else (if i < 216 then [w39, w65, w112, w142, w155, w172, w218, w231, w231] else [w39, w65, w112, w112, w142, w155, w172, w218, w231]))) else (if i < 220 then (if i < 218 then [w22, w65, w77, w112, w142, w155, w218, w218, w231] else (if i < 219 then [w22, w25, w65, w77, w112, w142, w218, w231] else [w22, w25, w65, w77, w112, w142, w155, w218, w231])) else (if i < 222 then (if i < 221 then [w22, w65, w77, w112, w142, w155, w161, w218, w231] else [w22, w65, w77, w92, w112, w142, w155, w218, w231]) else (if i < 223 then [w22, w65, w77, w112, w142, w155, w218, w231, w241] else [w22, w65, w77, w101, w112, w142, w155, w218, w231])))))))) else (if i < 336 then (if i < 280 then (if i < 252 then (if i < 238 then (if i < 231 then (if i < 227 then (if i < 225 then [w22, w65, w77, w112, w142, w155, w218, w231, w234] else (if i < 226 then [w22, w65, w77, w95, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w224, w231])) else (if i < 229 then (if i < 228 then [w22, w65, w77, w105, w112, w142, w155, w218, w231] else [w22, w26, w65, w77, w112, w155, w218, w231]) else (if i < 230 then [w22, w26, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w231, w249]))) else (if i < 234 then (if i < 232 then [w22, w65, w77, w112, w141, w142, w155, w218, w231] else (if i < 233 then [w22, w65, w77, w112, w142, w155, w218, w231, w247] else [w22, w65, w77, w112, w142, w155, w217, w218, w231])) else (if i < 236 then (if i < 235 then [w22, w65, w65, w77, w112, w142, w155, w218, w231] else [w22, w43, w77, w112, w142, w155, w218, w231]) else (if i < 237 then [w22, w43, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w139, w142, w155, w218, w231])))) else (if i < 245 then (if i < 241 then (if i < 239 then [w22, w49, w65, w77, w112, w142, w155, w218, w231] else (if i < 240 then [w22, w65, w77, w112, w142, w155, w218, w231, w237] else [w22, w60, w65, w77, w112, w142, w155, w218, w231])) else (if i < 243 then (if i < 242 then [w22, w65, w77, w88, w112, w142, w155, w218, w231] else [w22, w53, w65, w77, w112, w142, w155, w218, w231]) else (if i < 244 then [w22, w65, w77, w112, w142, w155, w218, w230, w231] else [w22, w58, w65, w77, w112, w142, w155, w218, w231]))) else (if i < 248 then (if i < 246 then [w22, w65, w77, w77, w112, w142, w155, w218, w231] else (if i < 247 then [w22, w39, w65, w112, w142, w155, w218, w231] else [w22, w39, w65, w77, w112, w142, w155, w218, w231])) else (if i < 250 then (if i < 249 then [w22, w65, w77, w112, w132, w142, w155, w218, w231] else [w22, w65, w72, w77, w112, w142, w155, w218, w231]) else (if i < 251 then [w22, w65, w77, w112, w142, w155, w218, w231, w239] else [w22, w65, w76, w77, w112, w142, w155, w218, w231]))))) else (if i < 266 then (if i < 259 then (if i < 255 then (if i < 253 then [w22, w65, w77, w112, w142, w155, w218, w231, w256] else (if i < 254 then [w22, w65, w75, w77, w112, w142, w155, w218, w231] else [w6, w22, w65, w77, w112, w142, w155, w231])) else (if i < 257 then (if i < 256 then [w6, w22, w65, w77, w112, w142, w155, w218, w231] else [w22, w22, w65, w77, w112, w142, w155, w218, w231]) else (if i < 258 then [w22, w65, w77, w112, w117, w142, w155, w218, w231] else [w1, w22, w65, w77, w112, w142, w155, w218, w231]))) else (if i < 262 then (if i < 260 then [w22, w65, w77, w112, w142, w155, w218, w231, w235] else (if i < 261 then [w16, w22, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w68, w77, w112, w142, w155, w218, w231])) else (if i < 264 then (if i < 263 then [w14, w22, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w82, w112, w142, w155, w218, w231]) else (if i < 265 then [w13, w22, w65, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w225, w231])))) else (if i < 273 then (if i < 269 then (if i < 267 then [w20, w22, w65, w77, w112, w142, w155, w218, w231] else (if i < 268 then [w22, w65, w77, w112, w142, w155, w218, w231, w245] else [w22, w65, w77, w112, w142, w155, w171, w218, w231])) else (if i < 271 then (if i < 270 then [w22, w65, w77, w112, w142, w155, w218, w231, w257] else [w22, w65, w77, w112, w142, w155, w169, w218, w231]) else (if i < 272 then [w22, w65, w77, w112, w142, w155, w186, w218, w231] else [w22, w65, w77, w106, w112, w142, w155, w218, w231]))) else (if i < 276 then (if i < 274 then [w22, w43, w77, w112, w142, w155, w172, w218, w231] else (if i < 275 then [w22, w65, w77, w112, w142, w155, w216, w218, w231] else [w22, w57, w65, w77, w112, w142, w155, w218, w231])) else (if i < 278 then (if i < 277 then [w22, w39, w65, w112, w142, w155, w172, w218, w231] else [w22, w65, w77, w112, w142, w155, w202, w218, w231]) else (if i < 279 then [w22, w65, w74, w77, w112, w142, w155, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w231, w258])))))) else (if i < 308 then (if i < 294 then (if i < 287 then (if i < 283 then (if i < 281 then [w65, w77, w112, w142, w155, w172, w218, w231, w258] else (if i < 282 then [w0, w22, w65, w77, w112, w142, w155, w218, w231] else [w0, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 285 then (if i < 284 then [w65, w77, w112, w117, w142, w155, w172, w218, w231] else [w1, w65, w77, w112, w142, w155, w172, w218, w231]) else (if i < 286 then [w65, w77, w112, w114, w142, w155, w172, w218, w231] else [w16, w65, w77, w112, w142, w155, w172, w218, w231]))) else (if i < 290 then (if i < 288 then [w65, w68, w77, w112, w142, w155, w172, w218, w231] else (if i < 289 then [w14, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w66, w77, w112, w142, w155, w172, w218, w231])) else (if i < 292 then (if i < 291 then [w13, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w113, w142, w155, w172, w218, w231]) else (if i < 293 then [w20, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w92, w112, w142, w161, w172, w218, w231])))) else (if i < 301 then (if i < 297 then (if i < 295 then [w65, w77, w112, w142, w155, w186, w218, w231, w245] else (if i < 296 then [w65, w77, w95, w112, w142, w155, w172, w218, w249] else [w65, w77, w112, w142, w155, w172, w218, w231, w242])) else (if i < 299 then (if i < 298 then [w65, w77, w109, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w172, w218, w231, w249]) else (if i < 300 then [w65, w77, w112, w142, w155, w202, w218, w231, w245] else [w65, w77, w112, w142, w155, w168, w172, w218, w231]))) else (if i < 304 then (if i < 302 then [w56, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 303 then [w39, w65, w112, w142, w155, w161, w172, w218, w231] else [w65, w77, w112, w142, w155, w216, w218, w231, w245])) else (if i < 306 then (if i < 305 then [w65, w77, w112, w142, w155, w166, w172, w218, w231] else [w64, w65, w77, w112, w142, w155, w172, w218, w231]) else (if i < 307 then [w4, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w172, w218, w231, w248]))))) else (if i < 322 then (if i < 315 then (if i < 311 then (if i < 309 then [w65, w77, w111, w112, w142, w155, w172, w218, w231] else (if i < 310 then [w65, w77, w112, w142, w155, w172, w218, w229, w231] else [w65, w77, w107, w112, w142, w155, w172, w218, w231])) else (if i < 313 then (if i < 312 then [w39, w65, w112, w141, w142, w155, w172, w218, w231] else [w65, w77, w112, w136, w142, w155, w172, w218, w231]) else (if i < 314 then [w45, w65, w77, w112, w142, w155, w172, w218, w231] else [w39, w65, w92, w112, w142, w155, w172, w218, w231]))) else (if i < 318 then (if i < 316 then [w65, w77, w112, w128, w142, w155, w172, w218, w231] else (if i < 317 then [w55, w65, w77, w112, w142, w155, w172, w218, w231] else [w28, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 320 then (if i < 319 then [w65, w77, w112, w142, w155, w172, w218, w231, w240] else [w65, w77, w91, w112, w142, w155, w172, w218, w231]) else (if i < 321 then [w65, w77, w112, w142, w155, w172, w218, w231, w232] else [w65, w77, w90, w112, w142, w155, w172, w218, w231])))) else (if i < 329 then (if i < 325 then (if i < 323 then [w65, w77, w112, w142, w155, w160, w172, w218, w231] else (if i < 324 then [w65, w77, w89, w112, w142, w155, w172, w218, w231] else [w65, w77, w102, w112, w142, w155, w172, w218, w231])) else (if i < 327 then (if i < 326 then [w65, w77, w95, w112, w142, w155, w172, w218, w234] else [w39, w65, w112, w142, w155, w172, w218, w231, w234]) else (if i < 328 then [w65, w77, w112, w142, w155, w216, w218, w231, w257] else [w65, w77, w112, w142, w155, w172, w218, w231, w238]))) else (if i < 332 then (if i < 330 then [w61, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 331 then [w3, w65, w77, w112, w142, w155, w172, w218, w231] else [w24, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 334 then (if i < 333 then [w65, w77, w112, w142, w155, w184, w218, w231] else [w65, w77, w95, w112, w142, w155, w184, w218, w231]) else (if i < 335 then [w65, w77, w112, w142, w155, w158, w172, w218, w231] else [w39, w65, w95, w112, w142, w155, w172, w218, w231]))))))) else (if i < 392 then (if i < 364 then (if i < 350 then (if i < 343 then (if i < 339 then (if i < 337 then [w65, w112, w130, w142, w155, w172, w218, w231] else (if i < 338 then [w65, w77, w112, w137, w142, w155, w172, w218, w231] else [w65, w95, w112, w130, w142, w155, w172, w218, w231])) else (if i < 341 then (if i < 340 then [w47, w65, w77, w112, w142, w155, w172, w218, w231] else [w49, w65, w77, w95, w142, w155, w172, w218, w231]) else (if i < 342 then [w65, w77, w108, w112, w142, w155, w172, w218, w231] else [w65, w77, w96, w112, w142, w155, w172, w218, w231]))) else (if i < 346 then (if i < 344 then [w65, w77, w101, w112, w145, w155, w172, w218, w231] else (if i < 345 then [w17, w65, w77, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w172, w218, w231, w241])) else (if i < 348 then (if i < 347 then [w65, w77, w112, w142, w155, w172, w218, w231, w243] else [w62, w65, w77, w112, w142, w155, w172, w218, w231]) else (if i < 349 then [w65, w77, w112, w142, w155, w186, w216, w218, w231] else [w39, w65, w101, w112, w142, w155, w172, w218, w231])))) else (if i < 357 then (if i < 353 then (if i < 351 then [w65, w77, w112, w138, w142, w155, w172, w218, w231] else (if i < 352 then [w48, w65, w77, w112, w142, w155, w172, w218, w231] else [w27, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 355 then (if i < 354 then [w65, w77, w112, w142, w155, w159, w172, w218, w231] else [w65, w77, w112, w142, w154, w155, w172, w218, w231]) else (if i < 356 then [w39, w65, w65, w112, w142, w155, w172, w218, w231] else [w39, w43, w112, w142, w155, w172, w218, w231]))) else (if i < 360 then (if i < 358 then [w39, w43, w65, w112, w142, w155, w172, w218, w231] else (if i < 359 then [w39, w65, w112, w142, w155, w172, w218, w231, w237] else [w39, w60, w65, w112, w142, w155, w172, w218, w231])) else (if i < 362 then (if i < 361 then [w39, w65, w112, w139, w142, w155, w172, w218, w231] else [w39, w49, w65, w112, w142, w155, w172, w218, w231]) else (if i < 363 then [w39, w39, w65, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w172, w218, w231, w236]))))) else (if i < 378 then (if i < 371 then (if i < 367 then (if i < 365 then [w38, w39, w65, w112, w142, w155, w172, w218, w231] else (if i < 366 then [w39, w65, w112, w120, w142, w155, w172, w218, w231] else [w32, w39, w65, w112, w142, w155, w172, w218, w231])) else (if i < 369 then (if i < 368 then [w39, w65, w71, w112, w142, w155, w172, w218, w231] else [w29, w39, w65, w112, w142, w155, w172, w218, w231]) else (if i < 370 then [w39, w65, w88, w112, w142, w155, w172, w218, w231] else [w39, w53, w65, w112, w142, w155, w172, w218, w231]))) else (if i < 374 then (if i < 372 then [w39, w65, w112, w142, w155, w172, w218, w231, w239] else (if i < 373 then [w39, w65, w76, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w132, w142, w155, w172, w218, w231])) else (if i < 376 then (if i < 375 then [w39, w65, w72, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w118, w142, w155, w172, w218, w231]) else (if i < 377 then [w38, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w120, w142, w155, w172, w218, w231])))) else (if i < 385 then (if i < 381 then (if i < 379 then [w32, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 380 then [w65, w71, w77, w112, w142, w155, w172, w218, w231] else [w29, w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 383 then (if i < 382 then [w39, w65, w112, w142, w155, w172, w218, w231, w258] else [w0, w39, w65, w112, w142, w155, w172, w218, w231]) else (if i < 384 then [w49, w65, w77, w132, w142, w155, w172, w218, w231] else [w65, w77, w112, w140, w142, w155, w172, w218, w231]))) else (if i < 388 then (if i < 386 then [w54, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 387 then [w65, w88, w112, w132, w142, w155, w172, w218, w231] else [w60, w65, w77, w112, w142, w155, w172, w218, w237])) else (if i < 390 then (if i < 389 then [w60, w77, w112, w142, w155, w172, w218, w231, w237] else [w65, w112, w132, w142, w155, w172, w218, w231, w239]) else (if i < 391 then [w7, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w103, w112, w142, w155, w172, w218, w231])))))) else (if i < 420 then (if i < 406 then (if i < 399 then (if i < 395 then (if i < 393 then [w65, w77, w93, w112, w142, w155, w172, w218, w231] else (if i < 394 then [w65, w77, w97, w142, w155, w172, w218, w231] else [w65, w77, w97, w142, w155, w172, w218, w231, w237])) else (if i < 397 then (if i < 396 then [w65, w77, w97, w112, w142, w155, w172, w218, w231] else [w40, w65, w77, w112, w142, w155, w172, w218, w231]) else (if i < 398 then [w65, w77, w112, w142, w155, w207, w218, w231] else [w60, w65, w77, w112, w142, w155, w207, w218, w231]))) else (if i < 402 then (if i < 400 then [w65, w77, w112, w123, w142, w155, w172, w218, w231] else (if i < 401 then [w65, w77, w112, w135, w142, w155, w172, w218, w231] else [w65, w77, w112, w133, w142, w155, w172, w218, w231])) else (if i < 404 then (if i < 403 then [w65, w77, w83, w112, w142, w155, w172, w218, w231] else [w46, w65, w77, w112, w142, w155, w172, w218, w231]) else (if i < 405 then [w49, w65, w77, w139, w142, w155, w172, w218, w231] else [w49, w77, w112, w139, w142, w155, w172, w218, w231])))) else (if i < 413 then (if i < 409 then (if i < 407 then [w63, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 408 then [w10, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w104, w112, w142, w155, w172, w218, w231])) else (if i < 411 then (if i < 410 then [w65, w77, w94, w112, w142, w155, w172, w218, w231] else [w65, w77, w99, w112, w142, w155, w172, w218, w231]) else (if i < 412 then [w42, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w179, w218, w231]))) else (if i < 416 then (if i < 414 then [w49, w65, w77, w112, w142, w155, w179, w218, w231] else (if i < 415 then [w65, w77, w112, w122, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w196, w218, w231])) else (if i < 418 then (if i < 417 then [w49, w65, w77, w112, w142, w155, w172, w221, w231] else [w65, w77, w112, w134, w142, w155, w172, w218, w231]) else (if i < 419 then [w65, w81, w112, w142, w155, w172, w218, w231] else [w49, w65, w81, w112, w142, w155, w172, w218, w231]))))) else (if i < 434 then (if i < 427 then (if i < 423 then (if i < 421 then [w65, w77, w81, w112, w142, w155, w172, w218, w231] else (if i < 422 then [w65, w77, w112, w142, w155, w212, w218, w231] else [w49, w65, w77, w112, w142, w155, w172, w218, w233])) else (if i < 425 then (if i < 424 then [w65, w77, w112, w125, w142, w155, w172, w218, w231] else [w53, w65, w88, w112, w142, w155, w172, w218, w231]) else (if i < 426 then [w36, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w73, w77, w112, w142, w155, w172, w218, w231]))) else (if i < 430 then (if i < 428 then [w44, w65, w77, w112, w142, w155, w172, w218, w231] else (if i < 429 then [w65, w77, w112, w121, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w172, w218, w231])) else (if i < 432 then (if i < 431 then [w65, w77, w112, w112, w142, w155, w172, w218, w231] else [w22, w65, w77, w112, w142, w155, w218, w231]) else (if i < 433 then [w22, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w161, w172, w218, w231])))) else (if i < 441 then (if i < 437 then (if i < 435 then [w65, w77, w92, w112, w142, w155, w172, w218, w231] else (if i < 436 then [w65, w77, w112, w142, w155, w172, w218, w231, w234] else [w65, w77, w95, w112, w142, w155, w172, w218, w231])) else (if i < 439 then (if i < 438 then [w65, w77, w112, w142, w155, w172, w218, w231, w241] else [w65, w77, w101, w112, w142, w155, w172, w218, w231]) else (if i < 440 then [w65, w65, w77, w112, w142, w155, w172, w218, w231] else [w39, w65, w112, w142, w155, w172, w218, w231]))) else (if i < 445 then (if i < 443 then (if i < 442 then [w39, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w132, w142, w155, w172, w218, w231]) else (if i < 444 then [w60, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w139, w142, w155, w172, w218, w231])) else (if i < 447 then (if i < 446 then [w49, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w88, w112, w142, w155, w172, w218, w231]) else (if i < 448 then [w53, w65, w77, w112, w142, w155, w172, w218, w231] else [w65, w77, w112, w142, w155, w172, w218, w231])))))))))

def sixE (i : Nat) : Nat :=
  let u : Nat := (if (i/16) < 7 then (if (i/16) < 3 then (if (i/16) < 1 then 0x3148953957e720ef4c52254e4e65c83bd694be5a85aa8ff5cda03046a16aa3fd73680be571598b1f5cda02704a153ea35736809c95f561a235cda02f94a153f02d73680c0971598b1f5ccc52726bd8f363c4f56ed099ee0b8ab841a02f94a15faa3573654be55f561a235cd70af94a153ea3573314add2842b84513da02f94a153ea3573 else (if (i/16) < 2 then 0x668895b1598c6aef5a02724a153ea3573680d0995e2ac43815a02704e5786ec6056809415f5f3a23815a4b3867ba7673ea2314d25714bd969385a03424e5786ec605314531823e27b2ef4c52254e4e6627bbd44abe59ed797875f8c52506bd6ab63bbd314895823e27b2ef4c50ba4e4e65c83bd42089539399720ef5512256bd6ab63bbd else 0x420addaf63cd8f13d9a2b769f7ced1c4f544add2842b84513d0814c608f89ecbbd4208953939989eef5082506bd6ab63bbd420895823e27b2ef5080ba4e4e65c83bd420b89b1561c6aef5ad2256bd6ab63bbd612895b1561c6aef4c52254e55fa27bbd3142e93957e720ef4c52e26c56631abbd314add2861084513d082254e55f9c83bd)) else (if (i/16) < 5 then (if (i/16) < 4 then 0x67aadd2842b84513cc532a4a10ae1144f5c2be59ed797875f9a03386099cf35697314941af3e2d8eef5512256bcf8b63bbd4209c9af63cd8f13cc5225608f8a70bbd314b89b1561c6aef59a2256c55871abbd314655a6c748d713cc52b74a10addec4f314d35a7e85b47384c52b769b1d235c4f3142e92842b84513cc532b69f7ced1c4f else 0x6809415f5f3c43815512254e4e65c83bd654be55f598a235cd12af967b5e5ded7e67abe52854fa8d5cda02104a153ea35735c28419ed797875f912a1067b5e5e1d7e314531823e29c2ef4c52726bd8f235c4f44abe59ed737875f8c52506bd6aa35bbd3142e93939989eef4c52e26c55867ebbd544895af5aa8d6ef59a2256c55867ebbd) else (if (i/16) < 6 then 0x314b85823e27b2ef4c52e16bd6ab63bbd314b8539399720ef4c52e16c55871abbd67ab8539399720ef5512504e4e65c83bd668b8939399720ef59ea25608f89ecbbd67a895af5aad8eef59ea256c55871abbd680be55f561a235ccc52256bd6ab63bbd314895b1561c6aef59a2254e4e65c83bd67a89539399720ef5a027257d586c7d73 else 0x544941823e27b2ef59a2e2608f89ecbbd314b85b1561720ef5a02f957d7ce88d73314895b1399c6aef59ea256c4e671abbd67a895826737b2ef59eaf96a1a163fd73314895b1399720ef59a2e26c4e671abbd680be5a86858ff5cd9a2256c4e671abbd680be5a154fc0b5cda02105c5662c7d7367abe571598b1f5cd1298a4e4e41ccbbd))) else (if (i/16) < 11 then (if (i/16) < 9 then (if (i/16) < 8 then 0x31469d39399720ef5a021057d58688d734a0629af6c7b54ef4c50ba608f89ecbbd3142e9af5aad8eef4c50ba6c55871abbd680c11a85aaa8d5cd952f96a16aa3fd73680be5a85aa8ff5cd9ea254e55f9c83bd298629823d97c4ef57098a6099cdf13bd668b89b1561720ef4c52e26c5585c83bd4209c9a6c748d713d9eae1608f89ecbbd else 0x3142e9b1399c6aef4c52e26c4e671abbd420895b1399c6aef4c52256c55fb1abbd680be57157eb1f5cd0814c4e4e6627bbd67ab853939989eef5082504e4e6627bbd420b893939989eef59a2e26c55871abbd66889583bf07d6ef59ea2560efc1f5bbd31489583bf07d6ef55122560efc1f5bbd44a62939390afcef55a2f957d58688d73) else (if (i/16) < 10 then 0x44aa89af6c7b54ef512b346c58d6b0bbd67ab85823e27b2f0d9eae14e4e65c83c3314adda161084513c5d18a4e4e41ccbbd314941823e27b2ef4c52504e4e65c83bd314941b1561c6aef5713346c58d6b0bbd67abe55f598a235ccc522560ef89ecbbd680be55f598a235cda02f969f53ed0d73314895b13999faef57130267b5e5e1d7e else 0x420895395d8720ef5512254e5761c83bd668895395d8720ef4c532a6bd8f363c4f680c112854fa8d5ccc52724a10aea344f314d35714bdb1f384c532b4a10aea344f680a8983e3c7e181570a5057d7ce88e0567a53139399720ef59ea504e4e65c83bd67a2e939399720ef59eae24e4e65c83bd680a89395e173381512a104e4e41ccbbd)) else (if (i/16) < 13 then (if (i/16) < 12 then 0x680d692854fa8d5cd082256bd6ab63bbd420895b1561c6aef4c52256c5585c83bd668895b1561720ef5512506bd6ab63bbd3142e9a84828d713cc527269b1d235c4f314addaf63cd8f13cc52b769b1d270c4f314d2595d069fb385512b769b1d235c4f314adda6e108d713d082504e4e65c83bd66894139399720ef4c52255f35f9ecbbd else 0x67aad139399720ef59eb2a4a10ae1144f3148958257e7b2ef5a934f4e4e65c83bd668b893939989eef59a34f6bd6ab63bbd668af939399720ef584ae24e4e65c83bd6a4b89af5aad8eef59a2e24e55f9c83bd5442e93957e720ef59a0ba4e55f9c83bd67ab853957e720ef59eae16c55871abc3544895823e27b2ef5512256c55871abbd) else (if (i/16) < 14 then 0x67ab897cd7eae6ef59eae2693a8a70bbd5f2d0128546a9f5cd9eaf96099cf35573314895af3e2d8eef59eb0269baf359d73680ce1a6ebcd675cd9eae26558862abbd420b8539399720ef5512e14e4e65c83bd668b8539399720ef59ea104a153ea35735c2c112854fa8d5cd70a724a153ea357331453183bf0720ef59eb46608f89ecbbd else 0x67acd182673cd4ef55134d65741a7ebbd420b85395d8720ef5512e14e5761c83bd668b85395d8720ef4c534965741a7ebbd67ad2995d069faef57098a4e5785ccbbd298b899ee9d9cf5f98230267ba7673d7e6a0d3d9ee9d9cf5f983b6267ba7673d7e680be5a7d7eb435ccc52256bd5fb63bbd544941af3e2d8eef4c52506bd6a9ecbbd))))
  (u >>> (66*(i % 16))) &&& 0x3ffffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 224 then (if i < 112 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x101 else (if i < 2 then 0x101 else 0x101)) else (if i < 5 then (if i < 4 then 0x101 else 0x101) else (if i < 6 then 0x101 else 0x101))) else (if i < 10 then (if i < 8 then 0x1d0000000000000000001d001d001d001d001d00000000000a05 else (if i < 9 then 0x1b3000001b301b301b301b301b301b300000000000a05 else 0x1b301b3000000000000000001b301b301b301b301b301b301b30000000000000d06)) else (if i < 12 then (if i < 11 then 0x1d001d00000000001d00c1001d0000001d0000010101000d06 else 0x1d001d000000000000001d001d001d001d001d00000000000a05) else (if i < 13 then 0x2700000000002700000027002700270027002700000000000a05 else 0x1d0000000000000000001d001d001d001d001d00000000000a05)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x1d000000000000001d001d00170027001d00020100000a05 else (if i < 16 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d000101)) else (if i < 19 then (if i < 18 then 0x1d000101 else 0x101) else (if i < 20 then 0x101 else 0x101))) else (if i < 24 then (if i < 22 then 0x101 else (if i < 23 then 0x101 else 0xd700d700d700d700d700d700d700d7000000000904)) else (if i < 26 then (if i < 25 then 0x6500000000003100030003000300030003000000000000000e07 else 0x101) else (if i < 27 then 0x6500650065006500650000000000650065000000000000000000650065006500650000000000000000001209 else 0x2d002d002d002d002d002d002d002d000000000804))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then 0x1b100b300b300b300b300b300b300b300b3000600000904 else (if i < 30 then 0x1b3000001b50000000000000000001d001d001d000000000000000000000a0a else 0xb700b700b700b700b700b700b700b7000000000804)) else (if i < 33 then (if i < 32 then 0x1d001d001d001d001d001d00000000000a05 else 0x101) else (if i < 34 then 0x101 else 0x101))) else (if i < 38 then (if i < 36 then 0x1b7000101 else (if i < 37 then 0x1f000101 else 0x19b000101)) else (if i < 40 then (if i < 39 then 0x3000101 else 0x3000101) else (if i < 41 then 0x1d000101 else 0x101)))) else (if i < 49 then (if i < 45 then (if i < 43 then 0x101 else (if i < 44 then 0x101 else 0x101)) else (if i < 47 then (if i < 46 then 0x101 else 0xb5000101) else (if i < 48 then 0x1000101 else 0xb7000101))) else (if i < 52 then (if i < 50 then 0x27000101 else (if i < 51 then 0x1000101 else 0x1d000101)) else (if i < 54 then (if i < 53 then 0x65000101 else 0x2d000101) else (if i < 55 then 0x1d000101 else 0x1d000101)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then 0x1d000101 else (if i < 58 then 0x1d000101 else 0x1d000101)) else (if i < 61 then (if i < 60 then 0x3000101 else 0x1d000101) else (if i < 62 then 0x1d000101 else 0x1d000101))) else (if i < 66 then (if i < 64 then 0x1d000101 else (if i < 65 then 0x1d000101 else 0x1d000101)) else (if i < 68 then (if i < 67 then 0x1d000101 else 0x1d000101) else (if i < 69 then 0x1d000101 else 0x1d000101)))) else (if i < 77 then (if i < 73 then (if i < 71 then 0x1d000101 else (if i < 72 then 0x1000101 else 0x1d000101)) else (if i < 75 then (if i < 74 then 0x1d000101 else 0xc1000101) else (if i < 76 then 0x1d000101 else 0x1d000101))) else (if i < 80 then (if i < 78 then 0x1d000101 else (if i < 79 then 0x1d000101 else 0x1d000101)) else (if i < 82 then (if i < 81 then 0x1d000101 else 0x1d000101) else (if i < 83 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1b9001d001d001d001d001d001d001d001d000300000904))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then 0x1d0000006f001d001d001d001d001d001d000002000000000e07 else (if i < 86 then 0x301bb006d000000000003000001bb0000000001bb01bb01bb000001bb01bb01bb00030300000001000000011309 else 0x330033000300030003000300d9006700000000000300650000000000030003000300030000000000000100011309)) else (if i < 89 then (if i < 88 then 0xdd01bd00dd00dd00dd00dd00dd00dd00000000000a05 else 0xb3000000b301b100b300b300b300b300b300010000000b05) else (if i < 90 then 0x1bf00e100e100e100e100e100e100e100e1000002000904 else 0x1c1000000000003001d0000008d001d0000001d001d001d001d00010000000000000e08))) else (if i < 94 then (if i < 92 then 0x65000000000000000000650000016b006500000000006500650079006500650065006500000065006500650000000000000000000000160b else (if i < 93 then 0x1c301310131013101310131013101310131000700000904 else 0x2d002d002d002d002d002d002d002d000000000804)) else (if i < 96 then (if i < 95 then 0x100310001000100f3000100a100010001009f000100010001000100010002000000000000020000000100000000000101001515 else 0x1d001d001d001d001d001d001d001d000000000804) else (if i < 97 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804)))) else (if i < 105 then (if i < 101 then (if i < 99 then 0x1d001d001d001d001d001d001d001d000000000804 else (if i < 100 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1f001f001f001f001f001f001f001f000000000804)) else (if i < 103 then (if i < 102 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804) else (if i < 104 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1f001f001f001f001f001f001f001f000000000804))) else (if i < 108 then (if i < 106 then 0x1d001d001d001d001d001d001d001d000000000804 else (if i < 107 then 0x101 else 0x1b101970197019701970197019701970197000600000904)) else (if i < 110 then (if i < 109 then 0xc100c100c100c100c100c100c100c1000000000804 else 0x1d001d001d001d001d001d001d001d000000000804) else (if i < 111 then 0x1d000101 else 0x19b000101))))))) else (if i < 168 then (if i < 140 then (if i < 126 then (if i < 119 then (if i < 115 then (if i < 113 then 0xd7000101 else (if i < 114 then 0x1c500000000000001c501c501c501c501c501c500000000000a05 else 0x1c70000000001c701c701c701c701c701c701c700000000000a05)) else (if i < 117 then (if i < 116 then 0x1c90000000301cb01cf01cd0000000000030003000300000000000000000000000000000e0e else 0x6500000000003100030003000300030003000000000000000e07) else (if i < 118 then 0x6500000000003100030003000300030003000000000000000e07 else 0x3000101))) else (if i < 122 then (if i < 120 then 0x1d000101 else (if i < 121 then 0x60065006500000000000000650000000a00650031000000000065000000650065006500650065006500650001000200000000000000170b else 0x1d000101)) else (if i < 124 then (if i < 123 then 0x300200000000000000003003b00000003002200000000000300000000000300030065000000030003000300030100000000000001010000170b else 0x3006500000000000000000000003100030003000300030003000000010000000e07) else (if i < 125 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804)))) else (if i < 133 then (if i < 129 then (if i < 127 then 0x1d001d001d001d001d001d001d001d000000000804 else (if i < 128 then 0x1b301b300000000000001b3000001b301b30000001201b301b300000000000001b301b301b301b300000000000000020000150a else 0x2500000000002500250025002501270025002500000103000a05)) else (if i < 131 then (if i < 130 then 0x710071007100710071007100710071000000000904 else 0x2d002d002d002d002d002d00000000000a05) else (if i < 132 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804))) else (if i < 136 then (if i < 134 then 0x1d001d001d001d001d001d001d001d000000000804 else (if i < 135 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804)) else (if i < 138 then (if i < 137 then 0x65000101 else 0x2d000101) else (if i < 139 then 0x1d000101 else 0xb3000101))))) else (if i < 154 then (if i < 147 then (if i < 143 then (if i < 141 then 0x1000101 else (if i < 142 then 0x1d000101 else 0x1d000101)) else (if i < 145 then (if i < 144 then 0xe5000101 else 0x1d000101) else (if i < 146 then 0x1d000101 else 0x1d000101))) else (if i < 150 then (if i < 148 then 0x1d000101 else (if i < 149 then 0x3000101 else 0x1d000101)) else (if i < 152 then (if i < 151 then 0x1d001d001d001d001d001d001d001d000000000804 else 0xe500e500e500e500e500e500e500e5000000000804) else (if i < 153 then 0x65004c00650000006500000065003b0065004e00650065006500000065006600650065000000650065006501000000000000010000000102001c0e else 0xf3001d000000000000001d001d001d001d001d0000000000000d06)))) else (if i < 161 then (if i < 157 then (if i < 155 then 0x27004401c100000135000001c10000000001d1000001c101c10000000000000002010000000000000f0f else (if i < 156 then 0xe50000000000e500e900eb000000e50000001d00e500e50060000000e5010200000502000f07 else 0xbb0065000000bb0000000000650065000000bb000000bb00bb000000000000000000000100000d0d)) else (if i < 159 then (if i < 158 then 0x101 else 0x1d001d001d001d001d001d001d001d000000000804) else (if i < 160 then 0xc600650065006500000000006500a4000000860065003100a800650065008a0065000000650000006500650000000103000000000000020100001e0f else 0x1d000101))) else (if i < 164 then (if i < 162 then 0x6500f00000000000650000006500000065000000000000006500000086006500650065006500650065006500650000000000000001010000170b else (if i < 163 then 0x6500650000006500000000000000650000006500f00065002c000000650031006501d300a40065006501d50065006500650065000001050008000002000100001a0d else 0x65006500000065000000650000000000650065006500c60000006500650001010000000000000001000000000000000000001515)) else (if i < 166 then (if i < 165 then 0x650031006501db000001d900000065000000650065000000650000006501d700650001000000010001001209 else 0x1b100cd00cd00cd00cd00cd00cd00000100000b05) else (if i < 167 then 0xd700d701b300d701b50000000000d700d700d700000000000000000000000000000e0e else 0xc100c100c100c100c100c100c100c1000000000804)))))) else (if i < 196 then (if i < 182 then (if i < 175 then (if i < 171 then (if i < 169 then 0x1d000101 else (if i < 170 then 0x2d002d002d002d002d002d002d002d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804)) else (if i < 173 then (if i < 172 then 0x1d001d001d001d001d001d001d001d000000000804 else 0x1d001d001d001d001d001d001d001d000000000804) else (if i < 174 then 0x101 else 0x101))) else (if i < 178 then (if i < 176 then 0xcf00cf00cf00cf00cf00cf00cf00cf000000000904 else (if i < 177 then 0xc100c100c100c100c100c100c100c1000000000804 else 0x1d001d001d001d001d001d001d001d000000000804)) else (if i < 180 then (if i < 179 then 0x1d001d001d001d001d001d001d001d000000000804 else 0xc100c100c100c100c100c100c100c1000000000804) else (if i < 181 then 0x27000101 else 0x1dd0000006500010001000100010001000100000000000a05)))) else (if i < 189 then (if i < 185 then (if i < 183 then 0x1990199019901990199019901990199000000000904 else (if i < 184 then 0x1df0000006500010001000100010001000100000000000a05 else 0x27000000270027002700270027002700000000000a05)) else (if i < 187 then (if i < 186 then 0x650000006500010001000100010001000100000000000a05 else 0x1d000101) else (if i < 188 then 0x30000008d0000000000000000001d001d001d000000000000000000000a0a else 0x1d3000001d300010001000100010001000100000000000a05))) else (if i < 192 then (if i < 190 then 0x27000000270027002700270027002700000000000a05 else (if i < 191 then 0x1d000101 else 0x650000006500010001000100010001000100000000000a05)) else (if i < 194 then (if i < 193 then 0x1d000101 else 0x1b30000002d002d01b5002d002d002d00000001000a05) else (if i < 195 then 0x26002c0020002e002200320040001d001d004c006f00000003001d001d002f001d0025001d0003001d001d0027001d0001001d0023001d001d001d0021001d001d001d001d001d000d001d006d001d0029001d001d001d001d001f001d001d001d002d0001001d0001001d002b001d240000002a000000020000001e37002c1736002c1235002c0734002c0033002c0d32032c0431002c1e2e032c582c else 0x3000000230000000000000001001d00000000006d001d001f002100010000001d00010003001d000100000001000000010001001d000100040001010002010400000200001d0e))))) else (if i < 210 then (if i < 203 then (if i < 199 then (if i < 197 then 0x1d00840060006400a000e0008000c000000020002000200020000800000c0400001108 else (if i < 198 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d else 0xa5001d00a3001d0000001d0031009b002300010001009d0000009f00010001001d001d0001001d00a100010021001d0001000100010001000600030d0802010e0101100a0006030002022613)) else (if i < 201 then (if i < 200 then 0x1f001d00000000001f001d00000000001d001f001f0000001d001f0000001f001f00010000001d0000001f001d001f001f0300010002020003020001000100001e0f else 0x23002300a3001d001d00010001002300230023001d0000002300230005000000000000000000000000000000000000002300230023001d001d001d001d0023000c00120008000500040012000000052010) else (if i < 202 then 0x300000065001d00030120000000030003001d0000001f0003001d0003001d0003000300a70003001d00270003000100000031010c00a9000301000003010e0102001d0000012c00000003000300001400000c0b00000200000017071e00201100000a05003018 else 0x2300ab001d0000001d001d000000710025001d0000000700000000000000000000009b0000001d00000000000000000000001d001d001d01000701000002010000020100000005002211))) else (if i < 206 then (if i < 204 then 0x1d001d000000000000001d00000000001d001d0000001d001d00000000001d001d00010000001d00010000001d001d001d0000010000010003000000000000001e0f else (if i < 205 then 0x2d000d000000000001001d002f00000000001d006f00000027002500000029001d00010001002b001d000100010001001d000101000114000000140100010100001d0e else 0x1d00c600c000c2014000ac00ae00b200000040004000400040000800000c0400001108)) else (if i < 208 then (if i < 207 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d else 0x16c000000000000000000030000000000a300000000001d0000002300ad00b1000300030003006d001f00a3001d00af0003009f00030021000000010095006500370003000300000501000c040000070311000b0010000008002814) else (if i < 209 then 0x2d001d002d0000002d001d002d001d002d0180002d001d0182001d002d001d0001002d0000002d002d002d01000103000004020001020000010601012211 else 0x1d0003000000630027001d0001001d009500a700270001001d00a9001d00010001000000000000001d000000010001000100040100000a020000020200000200002110)))) else (if i < 217 then (if i < 213 then (if i < 211 then 0x1a0000001ce000001a20065001d000100b30206001d006500b500010001001d01cc00b7001d0001006501e000010001000000010001001d000100000b13000202130102070202000804000300010c002c16 else (if i < 212 then 0xd00bb000000b9002700190001002d0011002b001d00bf001d002b002b006f0029001300bb00bd001d003700950000002b00000000002b001d0d01020e0a0108000e0100120001050001012412 else 0x1d001d000000000000001d00000000001d001d0000001d001d00000000001d001d0001001d00000001001d001d001d0104000100000000000000000001001e0f)) else (if i < 215 then (if i < 214 then 0x100200020000301 else 0x200020001d0000000303) else (if i < 216 then 0x400040001d0000000303 else 0x4000400001000000000304))) else (if i < 220 then (if i < 218 then 0x1d00200020000301 else (if i < 219 then 0x224024202600020024c0234026e002e006000600060006000080000000400001008 else 0x1d000101)) else (if i < 222 then (if i < 221 then 0x20002000010001000303 else 0x200000001f0000000303) else (if i < 223 then 0x20001d0020000100000304 else 0x200020001d0000000303)))))))) else (if i < 336 then (if i < 280 then (if i < 252 then (if i < 238 then (if i < 231 then (if i < 227 then (if i < 225 then 0x2300200020000301 else (if i < 226 then 0x2a00020030002c00020028002e0032000030000000003000000000909 else 0x100000020000301)) else (if i < 229 then (if i < 228 then 0x200000001d0000000303 else 0x3800242036000200240022003400022008000800080008000080000000400001008) else (if i < 230 then 0x1d000101 else 0x1d00000020000301))) else (if i < 234 then (if i < 232 then 0x200000001d000000000304 else (if i < 233 then 0x1d00200020000301 else 0x200020001d0000000303)) else (if i < 236 then (if i < 235 then 0x2000010001000303 else 0x344026e0272002003cc034003a0004c00a000a000a000a000080000000400001008) else (if i < 237 then 0x1d000101 else 0x2000010000000303)))) else (if i < 245 then (if i < 241 then (if i < 239 then 0x400002004800460042003e00444002000010200000200000001000909 else (if i < 240 then 0xd04a000200200000403 else 0x20002d002004e004c001000300010505)) else (if i < 243 then (if i < 242 then 0x200020002b0000010303 else 0x200020001d0000000303) else (if i < 244 then 0x20002f0000010303 else 0x5000504056800200540052005240020001d0200000200000001000909))) else (if i < 248 then (if i < 246 then 0x200020001d000000000304 else (if i < 247 then 0x36402600264002003c0036003a0004000c000c000c000c000080000000400001008 else 0x1d000101)) else (if i < 250 then (if i < 249 then 0x2005800020000300000000000405 else 0x2005c0002005a0001d01010000000505) else (if i < 251 then 0x20001d0000010303 else 0x68c06040000066005e0002006200640001d0503000000000000000909))))) else (if i < 266 then (if i < 259 then (if i < 255 then (if i < 253 then 0x200020001d06a000010100000405 else (if i < 254 then 0x6c4002006c0001d00000000000505 else 0x244024003c0002c024c025003cc002000e000e000e000e000080000000400001008)) else (if i < 257 then (if i < 256 then 0x1d000101 else 0x1d00200020000301) else (if i < 258 then 0x20000006e00000000000000020001d000000000804 else 0x2007000001000000020000000405))) else (if i < 262 then (if i < 260 then 0x1d00200020000301 else (if i < 261 then 0x1d002000200000000303 else 0x1d00200020000301)) else (if i < 264 then (if i < 263 then 0x1000000200000000303 else 0x200020001d0001000303) else (if i < 265 then 0x20001d0020000000000304 else 0x1d00000020000301)))) else (if i < 273 then (if i < 269 then (if i < 267 then 0x200000001d000301 else (if i < 268 then 0x1d002000000202 else 0x1d002000000202)) else (if i < 271 then (if i < 270 then 0x1d002000000202 else 0x724002007400720078007440760001d010101010002010807) else (if i < 272 then 0x6d002000000202 else 0x1d002000000202))) else (if i < 276 then (if i < 274 then 0x1d000101 else (if i < 275 then 0x6f002007a00200000303 else 0x7c007c4001d002002000100000405)) else (if i < 278 then (if i < 277 then 0x1d000101 else 0x1d002000000202) else (if i < 279 then 0x8040840000007e407e00000002008200800001d0000000001000000000a09 else 0x2000200020002000200020001d00200020000200000904)))))) else (if i < 308 then (if i < 294 then (if i < 287 then (if i < 283 then (if i < 281 then 0x10000001d001d0000000000000000000000000000000000000000000000000000001d001d001d001d0000010000020101000001000002040100000103002a15 else (if i < 282 then 0x200020000000200000001d0020000000000904 else 0x1d00000001001d001d00000000001d001d00000000001d0000001d001d0000001d001d00010000010d000b010000020000010100000101002a15)) else (if i < 285 then (if i < 284 then 0x860001d000000000000001d001d00000000001d00000000001d00000000001d00000001001d0001000000000000001d001d001d0001000200000100000001000000001f0f else 0x1000000000000000000000000002300a7000000030001001d088c00c1001f006d001d000000010021001d00010001000000ad00010000000100010001000005000000010000000100000d02002110) else (if i < 286 then 0x1d001d000000000000001d001d00000000001d00000000001d001d0000001d001d00000001001d000000000000001d001d001d001d00000000000000000201000200001d0e else 0x1d0003001d000d001d001d00000000001d001d00000000001d0000001d001d0000001d001d00a70023001d002d001d00c3001d001d001d000402000003000000010200000101002110))) else (if i < 290 then (if i < 288 then 0x1d00000000001d001d00000000001d001d00c100000000001d0000001d00010001001d001d001d00000000001d001d001d00000100000000050100000100001d0e else (if i < 289 then 0xd002d0000002b001d002f0029001d006f001d001d002500270001001d001d0001000100b90001000000010001000100010100000900010f0001000800001f0f else 0x1d00000000001d001d00c10000001d001d000000000000001d0000001d00010001001d001d001d00000000001d001d001d00000100000000050100000100001d0e)) else (if i < 292 then (if i < 291 then 0x1d001d00000000001d001d00000000001d001d00000000001d0000001d001d001d0003001d000000c5001d001d001d0101000100000000000000000001001e0f else 0x10001001d0003002300000027001d0001001d000000a7001f0001001d00a9001d000100c7000000030000001d0000000100010001000401000000020000130200001300002010) else (if i < 293 then 0x1d001d001d0000001d000000000000001d001d0000001d001d00000000001d0001001d001d001d002f001d001d001d0000000000000001000001010000001e0f else 0x101)))) else (if i < 301 then (if i < 297 then (if i < 295 then 0xcd00c900c900c900cb00d1001d0000000000c9000000d500c900cf00000000000000000000000000d30000010000c900d700c900c9000000020000010100020100001b0d else (if i < 296 then 0x30000000300030003001d08a80003000300670033000308d2000300d9000300030065000308e0007900030003000300030000010004020002050103070908000002082412 else 0x23001d000000a3002300000001001d0023000000050000000000000000000000000000002300000000000000000023002300230023001d0023002300030100030002010005060403020302002311)) else (if i < 299 then (if i < 298 then 0x3000000000000001d00000001001f0027000000a700000009001d00010001000300a90102000100000001001d001d0000000100010001000009000004030000000500000601002110 else 0x1d00400040000301) else (if i < 300 then 0x3001d000d001d000000db001d0000001d00d5001d000000000000001d001d01c0001d001d0000001d001d001d001d001d000000020000000000050100190c else 0x1d00000000001d001d00000000001d001d00010001001d001d001d000000000000000000000000000000000000001d001d001d001d000603000003000000020200000202002010))) else (if i < 304 then (if i < 302 then 0x10000000100e300a1000000df009f00dd000100010031002d000100e1096c0000001d00000027000109220001001d00000001000100010926001d0001000100010900001d01ce0000000101d2094000010001000100000000001f00000002080000001f1000001000000819003018 else (if i < 303 then 0x40000000010000000303 else 0xe5002d00e5018000e500e500e7006100e500e5001d0031098800eb00e500cf00e500db0000000000000000000000e9000000e500e500e500e5000304020002020000030200000000002010)) else (if i < 306 then (if i < 305 then 0x1d000000a3000000ed001d09ac09b0001d00a300a3001d0001001d00a3001d0001000000a30000001d00a3003d00a300a300a300a3030005070d02020203000307090002050401002713 else 0x186002d001d002d0000002d001d002d001d002d09c0002d001d0182001d002d001d0001002d0000002d002d002d01000103000004020001020000010601012211) else (if i < 307 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d else 0xef0023001d0000001d001d0000000100250000000000f10000001d00000000000000000000001d00000000000000000000001d001d001d01000601000002010000020100000006002311))))) else (if i < 322 then (if i < 315 then (if i < 311 then (if i < 309 then 0x1d0000000000000000001d000000000000001d00000000001d0001001d001d001d0000001d001d000100000000001d001d001d00010000000100000100000104001c0e else (if i < 310 then 0x1d00000000000000230000001d00a50001000000f300a3001d003109e0009f0001001d009d0001000100010000001d00a1000100010000000000010001000100010b0e00000c0a0902020001080101000000050002022b15 else 0x1f001d000000000000001d001f00000000001d001f0000001f001d0001001f001d001f0000001d001d0001001f001d001f001f001f01040003000101000100000104001c0e)) else (if i < 313 then (if i < 312 then 0x400040001d0000010303 else 0x490025000d00000000001d00f90000001d00f500000025002700f7001d00fb0001001d00fd00010000001d00010001000100010402000009020001000100020000001e0f) else (if i < 314 then 0x1001d0a260a40001d001d0a6c0a00001d001d00000a22001d0000001d001d0000001d001d000100000110000e0100000c0000010100000101002a15 else 0x1f00400000000301))) else (if i < 318 then (if i < 316 then 0x300fd001f001d001f0000001d001f001f001f001d001f001d001f001f001d001f001f001f00000000002b0000001f001f001f000d01000001000000040000001201002110 else (if i < 317 then 0x1d001d00000000001d0000001d001d0a800000001d0000001d0000001d0001001d0000001d001d001d01000102000101000001020000000000002211 else 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d)) else (if i < 320 then (if i < 319 then 0x2d00230000001d001d001d000300ff0000001d001d000d0000000000000000000000000000000000000000001d001d000000000000001d001d001d0000070000050000010100000001001f0f else 0x1d001d00000000001d001d0000000000000000001d00000000001d001d001d000100000000001d00010000001d001d001d000100000000000100000200000401002010) else (if i < 321 then 0x2d00230000001d001d001d00ab002500000000001d01010000000000000000000000000000000000000000001d001d000000000000001d001d001d0000070000050000010100000001001e0f else 0xaec0000000000010aa000010103001f001f001d001d00000000001f001f001f001f0ac2001d0000001f001d001f0b200b0c001f001f001f05080401000e000000131200130a06000000020c022a15)))) else (if i < 329 then (if i < 325 then (if i < 323 then 0x3000000000000010b0023001d0107001f00010001001d00000021006d001d001d010501090001000101070001000100030000001d00010000000100010001000b0108000003000004090000020b002110 else (if i < 324 then 0x1d000000000000001d000000000000001d001d0000001d001d00010000001d001d0b40001d0000001d001d00000101000201010000040000000100002211 else 0x1f001d000000000000001d001f00000000001d001f0000001f001d0001001f001d001f0000001d001d0001001f001d001f001f001f01040003000101000100000104001c0e)) else (if i < 327 then (if i < 326 then 0xb72000101 else 0x4000230000010303) else (if i < 328 then 0x6f000000eb006f00000000006f0200001d000000e9006f006f006f00e5006f00e5010d0000006f006f006f000007080000010000010100190c else 0x1d001d0001000100000000001d001d001d001d000000000000000000000000000000000000000000000000000000000000001d001d0000001d001d001d000000010000000000060004000000002010))) else (if i < 332 then (if i < 330 then 0x206000000010000002d00650111010f0115001d0001001d00010b800b82002d0051001d00010065000101130000001d000100010004010600000c040004020000000201012311 else (if i < 331 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d else 0x1d000000000000001d000000000000001d0bac001d0bb0000100c10bc0001d0ba40ba0001d001d001d001d0bcc001d001d001d001d09000000010000020000000809040b090201002613)) else (if i < 334 then (if i < 333 then 0x72602cc0be402ae028207520c200c0c00d700d708b0011d0100000300d700d7011700cf011f00d7000300d700d700d700d7011700d7011b00d700d700d7011700d700d700d700d700d7000d00d700c900d7011700d700d700d700d7011900d700d700d7012301170117011700d7012100d7240000002a000000020000001e38002c1737002c1236002c0735002c0034292c0d33032c0932002c1c31032c592c else 0xd7006500d7000300000cc000d70003000300d7011900000003000300d7000300d7000300030117010000310c80012500d7010000030c420c60000301000cac00d70003000300001100000c0b00000700000002051a001d1600000a05003018) else (if i < 335 then 0x1d000000000000000000000000001d00010027001f000000ab001f001d001d001f001d010e001d001d001f001d00250127001f001d01290000001d001d001d001d02050d000203060402100100090202000c0101001000002e17 else 0xd000c2200000c000ce000400c020c2000030503000000000000000909))))))) else (if i < 392 then (if i < 364 then (if i < 350 then (if i < 343 then (if i < 339 then (if i < 337 then 0x2ec0300000d00030b6608c60003006108e200330786005b02ee0003030200330d460043077200030cec08ca00030031006b005f000b012000030003005d000300030d200003006900670003000308e000310d6000030031006501200063012026160028021628010216040102032113250914052f1000052e0d00052307020d210d00051f0a00051d0900051b04005f2f else (if i < 338 then 0x63012c00310001001d00010031000d0027003b0061006f000d000000790067000300650160002f0029001d00310025001d000300930031006b0031000300310031006900310031000b0000003113200d1624000022030017110010081d1400120a000000080800341a else 0xca0000000000000000000030cc2000300030031000300030003000300310003012000030003000300310cc000650ca200000003012001200d80000300030000000000000e13000308000008090000050000000100003018)) else (if i < 341 then (if i < 340 then 0x1001d00000de0001d001d0dcc0da0001d001d0dce0da2001d0000001d001d0000001d001d000100000110000e0100000c0000010100000101002a15 else 0x65006500650000003100650e0c0e0e0065006500650160006500650d2000650065006500000065006500650000000100000000000008050001010000002512) else (if i < 342 then 0x1d0000000000000000001d000000000000001d00000000001d0001001d001d001d0000001d001d000100000000001d001d001d00010000000100000100000104001c0e else 0x10e00ab001d000300ab001d00430027012700a9001f00a7001d00ab001d000100ab000000ab001d00ab00ab00ab001d00ab06020e02000301070301000002010300002211))) else (if i < 346 then (if i < 344 then 0x101 else (if i < 345 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d000100270027001d00010000001d001d001d000001000000000200000000001a0d else 0x1d00000040000301)) else (if i < 348 then (if i < 347 then 0x1d002500bb001d0e200025001d0000001d00000025001d00010025002500ab000000250000000000000025002500000000012b0000002500000000002500250025001d00250200010b00070001000c0003000d000102032412 else 0x1a6000000000071002d0071001d00710027001d0000001d0e40007100270071001d0e62001d0001001d007100000071007100710001000601030f010001030000010501012311) else (if i < 349 then 0x10d000000000000010d012d01a0000000e7010d010d010d00e5000000000000000000000000010d00000000010d00cd00e7010d010d010000000103020001000202001b0d else 0x1d00400040000301)))) else (if i < 357 then (if i < 353 then (if i < 351 then 0xd002d0131000000000000001d01330000001d012f0025001d00270029013500010000001d00950001001d0001002b0001000100010503000003030004000100020000001f0f else (if i < 352 then 0x1001d0ee60ec0001d001d0f100e80001d001d0eae0000001d0000001d001d0000001d001d000100000110000e0100000c0000010100000101002a15 else 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d)) else (if i < 355 then (if i < 354 then 0x230003001f0001000100a70000001d001d001d00010000006d002100ad00000001000100a7001d000300210000000000010001000100010001000e00020000050000080500000300002110 else 0x230000000000000001001d000300000000001d00a5001d001d0001009d00a30021000000010001001d000000000003000100010001001d0000000804020005030200010002000005022010) else (if i < 356 then 0x4000010001000303 else 0x3a603a003a2004003ac03ae03b2004c014001400140014000080000000400001008))) else (if i < 360 then (if i < 358 then 0x1d000101 else (if i < 359 then 0x4000000f20000d000000000404 else 0xf4000400f420040002d00000000000505)) else (if i < 362 then (if i < 361 then 0x40004000010000010303 else 0xf800f820f600fa000400fa20fc6004000010200000200000001000909) else (if i < 363 then 0x1d00400040000301 else 0x1d00400040000301))))) else (if i < 378 then (if i < 371 then (if i < 367 then (if i < 365 then 0x1d004000400000000303 else (if i < 366 then 0x400040001d0001000303 else 0x4000010040000000000304)) else (if i < 369 then (if i < 368 then 0xfe00fe8004000400fe4001d04000000000605 else 0x400000004010001002000000000000000000011006010000000000000c07) else (if i < 370 then 0x2b004000000202 else 0x1d004000000202))) else (if i < 374 then (if i < 372 then 0x1d004000000202 else (if i < 373 then 0x4010200000104210400000106610801082001d0000000001000000000a09 else 0x4010a000030000000303)) else (if i < 376 then (if i < 375 then 0x10c2004010c0001d03000000000405 else 0x1d000001370023000000000001001d001d0000000000a50000001d00010000009d001d0001000100a3001d0003000100010001000100010001020500010000000300010100001f0f) else (if i < 377 then 0x1d001d0000001d001d000000000000001d00000000001d001d0000002d001d0000001d001d00030023001d001d000d001d001d001d0000000101000000020000000008001f0f else 0x1d001d000000000000001d000000000000001d00000000001d001d0000001d001d00000001001d0000001d0000001d001d001d001d00000000000000000201000200001d0e)))) else (if i < 385 then (if i < 381 then (if i < 379 then 0x23006d001d0000000001410003000000010000013b013d001d00010003001f013f01390021001100c100010139001d0001000100010000070d000c010a0100020800010300012311 else (if i < 380 then 0x1d0000001d001d001d001d10e80000001d001d000010e4001d10e0001d001d00010000001d001d001d001d001d00000103000301020100030000010000022311 else 0x1390000000000010025002d01391106000d002f001d11021100002700290001006f00010001001d00000001001d0001002b000100010001050f00070a03060300010004100006010501012613)) else (if i < 383 then (if i < 382 then 0x4000400040004000400040001d00400040000200000904 else 0x400040000000400000001d0040000000000904) else (if i < 384 then 0x112000650065119200b300651170009f1146006500b5006511740065114a00650143006500000065006500650000000101000101000105000001040005012412 else 0x3000000010000002711ac001d009500a7007d0095001d00a9001d009500000095001d0000001d009500950001000000950095009500950d01000a00000113070606000702000201032512))) else (if i < 388 then (if i < 386 then 0x1d006500000149014b001d0147001d001d01450001001d001d01e0000100b70001000100010000000000010001000101040601000c0000000006010b01001e0f else (if i < 387 then 0x37015501590143000001570000014f0000015101e0009f01430143003d014d015300370099006500000143003700370037003700370000020002020003020100090000011e0f else 0x11ca11c60100000203)) else (if i < 390 then (if i < 389 then 0x101 else 0x12000030003015900030003015f000000030000015b0039015d000300650003000300000000000101030000000000000000000000000000000000001a1a) else (if i < 391 then 0x1d00000000016111ec001d000000000000001d00000000001d00000000001d000000a70001001d001d0000001d006f001d00000001000200010000000100001c0e else 0x30163001d000000010165001d0003001d00010000001d0001001d0001001d00b7000100b501a2000100000000001d0001000000010001000100000600000f0d0000000400000701002010)))))) else (if i < 420 then (if i < 406 then (if i < 399 then (if i < 395 then (if i < 393 then 0x1f001d001d0000001f001d00000011001d001f001f018e001d001f0000001f001f00010000001d0000001f001d001f001f0d00010002020003020001000100001e0f else (if i < 394 then 0x4a0112c00651262016b0031058c006b128000651240006509821200058e016b1242016901600031016000651260000d0f20006510ac006507a6003100650d6c01600065006504a201670065005f0031000b123200650065006509800065016d006500650079016000312f0001270000012e00271a0b000003152604180301092e03142934042203260d2203110822040b0420091c0301041a00146231 else 0x16f0000015900000000000000000065016f000d00650065000d0073017101600031000d016d0171008d0031000d008d000d0160000d000d000d000d000000000000000d00000065000d0000000d000d0000000d000f0011001800070005000b000e00120100000d01082d16)) else (if i < 397 then (if i < 396 then 0xab016012c00173006500ef001f017500650000006512a0012c0065001d0065000312ec001d0065010d0206003100650065000100650065001d12ee006512c200010065006500651e010100000d051f071800171602081a08050b0315090007001d00170000023e1f else 0x1d001d000000000000001d00000000001d001d0000001d13041300001d00c10001001d001d00010000001d001d001d0001020104010100000001000000001e0f) else (if i < 398 then 0x7c605cc132411c605ae04c20f40002d002d06d200e5002d0003002d002d007110cc002d002d008f002d0087002d0003002d002d0180002d000101790057002d002d002d0083002d002d002d002d002d008d002d0177002d0089002d002d002d002d0049002d002d002d0001002d0001002d008b002d230000002d000000020000001d3a0020163900201138002006360020003500200c31032008340020282a0320592c else 0x180002d002d00000000002d0000002d002d01800000002d0000002d1340002d0001002d0180002d002d002d01000102000101000001020000000000002211))) else (if i < 402 then (if i < 400 then 0x23001d00230000019200030003000100010001001d006d0001001f001d00210001000100010001001d00010004000b010c0701000000010500070d0000000c03022d16 else (if i < 401 then 0x30023000000530000001d00010000001d017b004900230001017d001d00010001001d00950003001d000100010001000100010502030b00020301000100020200001f0f else 0x30023000001830000001d00010000001d0181001f009d00010021001d00010001001d017f0003001d000100010001000100010502030b00020301000100020200001f0f)) else (if i < 404 then (if i < 403 then 0xbd002d00bb000d000000bf001d00000000001d00b9006f002700bb0011001d0029001100010000002b000000000011001100110700010510010000000001020601001f0f else 0x1d13a60001001d001d138c1360001d001d138e1362001d0000001d001d0000001d001d00010000010d000b010000020000010100000101002a15) else (if i < 405 then 0x13d213d60100000203 else 0x13f2000101)))) else (if i < 413 then (if i < 409 then (if i < 407 then 0x1d0000000000000000001d0000002d0000001d002d002d001d0000002d002d001d001d002d001d0001001d00000000002d002d002d00000200000000000400030702001c0e else (if i < 408 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0185001d0000001d01850000001d001d001d000001000000000100000000001a0d else 0x1d0000000000000000001d000000000000001d00000000001d0001001d001d001d0000001d001d000100000000001d001d001d00010000000100000100000104001c0e)) else (if i < 411 then (if i < 410 then 0x650000000000000000001f00510001001d001d0001001f0065018900010000000101ce001d018b0001000100000187001d0001000000010001000100000700000b020100000200000101002010 else 0x650000001f00930003140e00010003001d00030027140c00030003001d00a7003100a9001d001d00030120001d0003000300030003000010150105000d030105010416000002010100012713) else (if i < 412 then 0x1d0000000000000000001d00001440001d001d14881444001d000100c1001d001d14241460001d001d1420001d001d0000001d001d09020000000000000200000708000a050100002613 else 0x11460526066c14a4064e03e207f20f8000b300b3108c010d01a0006500b300b300010001019300b3006500b300b300dd00b3000100b3019100b300b300b3018f00b300b300b300b300b3000d00b3010d00b3019500b300b300b300b3018d00b300b300b3019700010001000100b3000b00b3240000002a370000020000001e37002c1736002c1235002c0734002c0033002c0d32032c0931002c1e2e032c592c))) else (if i < 416 then (if i < 414 then 0x14c20000000000b301a000010065152414e0006501a00001000100b3154000b300010199006515000001000101a0000100b3000100010001040d01030313010e0802020005040003000205002c16 else (if i < 415 then 0x10000000000000000001d00030000001100030003006d00230000001d001d000101b200210001001f0001001f00010001000300000001001100010001001d00130a0a0c0e04071103070a000004070001010a0300012e17 else 0x2f001d001d001d001d002500030065046c1564001f0003001d01c0001d006f05121040006308060003000d0e0000230021001d001d001d01c0001d040e002d001d000b0622002900270003006d01c0001d13c6001d1164003b0fac001d01c0001d01c00003002a002d2a011f00290100011e0100032917150328140003130124030f010203210c00072016000304050a5b2d)) else (if i < 418 then (if i < 417 then 0x6500000000154015c40000006514c00001158c000101cc006500010001000115a00001000101cc00010001000100010000010b0001010701020001010008040006000000002c16 else 0x100000000000000000000002300000001001d019d006d00030021001d00270031019b0053001d0001000100a101d20027000100270001002100370000000100010001000100270017080a0c060e101503040e00000201000101050300012f17) else (if i < 419 then 0x54605ec042005ee0422085200b700b715f2000100b7006500b700b700e1102c00b700b701a100b7019f0011006500b700b701e000b7000100b7000500b700b700b7000100b700b700b700b700b7000d00b7000100b7000100b700b700b700b7018700b7000100b70113000100b7000100b7009900b7240000002e000000070000001e3a0021173900211238002107370021003600210d35032109320021292b0321582c else 0x15000000000000001502006500b7006516000001000100b715a000b715a20001006500b70001000101e00001000100b700010000000f0002020301020302020004010003000101002c16))))) else (if i < 434 then (if i < 427 then (if i < 423 then (if i < 421 then 0x1e00099001d000000b70000000100b7001d00b7001100b70003001d00b700b700b7001d00b70065002b00b7001d00b701390508001201030015030f0002000109000001070001012d16 else (if i < 422 then 0x1a3001d001d001d006f00250003001f082c001d02000001001d001d1620003106120fc0106c118c001d001d128813ec0001044600030023006d001d0001001d001d001d060e002b0442002d001d001d001d0001001d0001001d0200020001000127012a271327000200000215020002260e0102200d01020c0224020a0200021e03010e1d1901021c16005b2d else 0x650000000015240206000000651528000115c8000115c40065000100010001160000010001020600010001000100010000010b0001010701020001010008040006000000002c16)) else (if i < 425 then (if i < 424 then 0x1a7016c00000000000000000021008d001d001d00030003001d0000001d0003000301a900630023001d0000001f0212006d0003003b000300230003001d0003001d006d001f01a5001d002100010065000000000003000300010e1200080a10001f0100001d1f000001011b001600003018 else 0x101) else (if i < 426 then 0xbb00000000001d00bb000000000000001d00bb0000001d00bb00000000001d00bb009500010000001d001d001d002b001d001d000000000000010001000200001a0d else 0x1101ab00000000164c001d006501af01ad00b7164e001d0011001d0000001101e00001001100110011001d006500010011000000000011001d0004000903010d090f0804000201020007012412))) else (if i < 430 then (if i < 428 then 0x1d000000000000001d000000000000001d001d00000000001d00000000001d001d0001001d0000001d00010000001d001d001d000001000000000100000000001a0d else (if i < 429 then 0x1d000000000000006d000300a3001d002300b100210001001d000100ad00a3001f0001001d00af001d00030001000100000001000100010001000515000b00010a0202020001000000002211 else 0x46002c004c002800400034004e00240042008c00a6003000ac00c8020001b4008e01a001a8021401a4005201240180020801f4020400200160018c010000e801e801c801e401cc00e000860126014c012001e0006600c0012a010a00e40104016c006c020c010600b200c402100140006000ae01ac01d4010801d001b000000072012801ec00a2009200a001f00240006e010201c000820122008001c4022000622c0000003e0000004100000026504f111f4e4d11184c4b11084a491100484511103b35113934291133201911582c)) else (if i < 432 then (if i < 431 then 0x700090001028c002002e6000300200001000100030260028e0001000d0108000102ac0120002000010017000000030011002000e00015000f0001000501a0000100c0000101cc000100a002000001002000a201e0000100030003026201220001001b0001000100820001001300190072000b0020000100200104002000010000008002c00001002002030000003e0000003d0001021200303f0300053f2d2b2041273d2439201c1d38120019161100010b3100010c30082402170a013301006e37 else 0x4440280078002e00300026404400284030403c004e4026003e0040408c007e4038005e00620058405a4068004a005400900056408440660052000600480042408e0080408240600072004c403e4050006e008a004640700042003c403a006c0000007a005c0040003600384058007c0032003a40820064006c405c407e0004006a004e005a007600340072405600880046004c00840074006e407040800086003242c0000003e0000004100000026504f111f4e4d11184c4b11084a491100484511103b35113934291133201911582c) else (if i < 433 then 0x9c409a40944092409c0046607ac07c0032e046203320a4009e0001d003400290b6c001d09a000270ba000600a800a600a200060006000600a000ae00aa0006000600060002d000d0c40001d0940001d0b8000250b20001d0bc00021001d001d001f0b70001d0980001d001d0003001d0960001d00010001001d0920001d0b40001d0023001d001d0003002b0001002f001d001d0bec001d0c28001d0b8400010b440001001d0b00001d0b24001d001d0ac0001d0c00001d4b00340001000c002f002900470008000158000004570000245646001f5530000b54195609461b55044230540241005302401d52123c2c51153b0550043a004f213a104d343a8c46 else 0x100240031000000010d2e00010cc4000100200031000100800e880017003d003100010dc00e60001500010007000900390cf0001903400e140d0c00010dec0c920cec000500010d600e540001040600010c8e001300010001048c0080000f0cb000330080003100350011092e0037040200010db2000100050c64003b00010001093200010d8000010d32003300010dae001b00800e28000000010cc0003100010d400cac008000010c600001008054270901025100513c2300014e002f014c2709014903022036034846430342403103300804032a0100033c0129033b012503210100031f1c001816010039141100033a2b0d8a45)))) else (if i < 441 then (if i < 437 then (if i < 435 then 0x47003f0f000020001f001f0c600024102004ac03600045001f002100a0001f002700010f74001f0eac0c640000001f004300a00fa0002b00430041001f0f8800a00001000104260fe000a0001f00a00fc000a0001f094e004900a0001f0f4c001f0422001f0f20001f002f000d0fc41008001f001f0952001f0ee00001001f00290fe40001001f0ec0001f3d2e0100032a01001c3c2d002402061d412e01330302284303032300030222391c023c0918023b3637351a1518021411180c0a07180033001800430018023103208241 else (if i < 436 then 0x10480cc210540cce10440cc01050110603c0002303ce004b106000230ccc004f09660020000000c010ec10e000c003cc00c000c000c010a6002c000010c0097203c21080108c00c000230023002300230051000b00230023002310cc004d0003002310b200c0000500230057004100050023002300c0000d00530023002300230005005500230005106c002300c0002300230023005900230023002300230005000527050300004b2700004a430002490000214800000247000002463f000d4503490e3d1d40083a05390238034803371846201e173018361131002d022f020a122e102d8442 else 0x1142116c124c006b114e098603ec03e003ee116211cc1060114c00030003005b0043116e0000124000e000310020114003e20003112611ec00e011c011a0122000e0106c000300e000030003006900330992000b002c0003000d0067000300e0005d11800003118200330cac00030fee00310ca2000311600ca0122c00e011ac11e000e000030fe20061118c00030fe00003000300650003120c00630003118e0003005f000300030003000300031200000300030cae00030fec003100311254185d025a284f390005003700351930484d5858004c000000240027002e00151c474b2b580359051d2858134a2457101d2456001d45460320243605200c4408420640053e061f001d944a)) else (if i < 439 then (if i < 438 then 0x6d001d04c204d2002c002500001268001d001d0e20001d00211276001d0e30001d12ac12a4001d00000024001d006f001d001d002f0390038009ae001f0007001d001d12ca12f00100001d0100001d001d00351290001d002901000c86001d0cd0005f09a613000023001d12800023001d01000cc0001d005f01001330001d1310002d0071001d001d001d00070100132000731346001d0025001d12e0134e001d010000270c8e0007010000034f4c134a002c020300490253114602034843020311413f40113b133c112a33052826230500203a08311a39081c163835181253340010520f0e080708041d3201008643 else 0x2700251360001d001d006d1404002003b00075001d001d000113ca001f03a0001d0120001d00000fe41370002b000300230fb213f600030001001d0fec0120001d000104e6012013e8140c001d001d001d0fa20120006f12a0001d012012b00120001d04ee002d0120001d13b0001d09c2001d1390001d002f01200030001d001d13a000010077000d0001001d0000001d09d2001d1380001d0100010001360100014401000e002a1d4438014a0100304901032f0001002a1f2900442422003d411e1b1a150f0d14111c0c030a18003f0018004a003b0037072d8241) else (if i < 440 then 0x9020001ac00370001007901e000310005001700010015000105060031066c003b0220050200190001000f000105000140000101c801e8020406720001014001b4000701c0000000010001007b01400001000000010001000101c4001300010240066e00010001001b01e4002b01400001003100311420020800110001002b01b0018c000101401c242001001c1a00413d00013c3800010236000136350001342d00012c17001412170c0131012b2a2605001b0804243b0d3e0b010225006e37 else 0x68602a0052c02c8068002a8052e02c406820d000f0602a40ea01088158015280d0214c014c814a814c405321364146015881488158402c01440018012e011a815681548156414e011a00d8613661420136015600a461080136a12ea11a412e4000009ec14a012e60ea6108414a415000a400ea2152014e812e814e41524016009f2136814800f020d060f00148415c009ee12e215400d8213620d80154415a00a422c0000003e0000004100000026504f111f4e4d11184c4b11084a491100484511103b35113934291133201911582c))) else (if i < 445 then (if i < 443 then (if i < 442 then 0x6a6054c06a0054e06a216ac001d0552002917201600018015e00180178001801760018016c0000d1708001d1740001d16800027166000011500001d001d001d001f16b0001d146c001d1684001d16640003001d1628001d1700001d1648002516e0001d00030021006f001d001d001d1624001d0001001d16e8001d16c40001001d014c006d17040001001d16c8001d16e4001d001d00231688001d0180002b00011620002f002d001d0ac0001d1668001d1644001d001d1640001d16b4001d0b00001d58004a00010022004b003f0058000f00010000003a0048003800460021003000210000611c1334601713305f0413345e0413425d2a562c5a115418450652003e27500b2009138c46 else 0x67180018c4007f0020014c0000074605ac06c005ae06c20a1218ec17e001a017c001a0189217a001a01860006b000d006900430003000b003701a000031660003301a000031356190c148c00030dc0182c01a0003718b40037000300030003005b00650003130e0037005f00030003005d007d000318c8000310cc0003003700030db20003135200630003192c000310b20003184c0003130c000300030db6006101a0006500030dc2000318b000030003000036003f00260057003d57540053002f003d001d533a51150601000052365100062a51264922501e47014f0007324e1907014d002f0d460a07164c0544013913070b3319078c46) else (if i < 444 then 0xf4000490071008700811982002d002d19b0002d01c0002d002d01400000002d000313a40085002d005705c006ee0001196201c0002d077219e405c20001002d000312200a260001000101c0002d002d19c006ec008f19600083008d002d18400001002d01c01a2c14a013a81980002d1820002d19e8002c0089002d00010f421952002d01c019b40000008b01c0002d002d002d1a0c168c4a48094542320528413e3d000000090000473a0000462700440027380000092d290226242202320a3602050a351d090a2e12051d301b190e1712090a000d05040b02058643 else 0x201a8c17c00140070c0560070e05621ab20a7214c00000062601e001e000011a4001e0009100011ad400130009162c0001000700110001130800010063000100010091009510c0000100630019000f0001009300010d40186c006300010015001b000100011ae4000100631ae800011b0c00010d32000101e0000101e000171a60000100310001000100010001000100970d42000100010001006300050d3600011ad0006300010001130400110001220010002a003600000009001b56184b391840003c553800345409001d531a4b0a492f532d1910520419105100192d502919104f0b46164e1019264d45190b4000198542)) else (if i < 447 then (if i < 446 then 0x12201c801cac1a4006461a6000650ee21c6613a002001bc017a01b6202001be8072c1b9001401bac072e1b4200000001000100110001001300650ee0020000011bc2020005801be4002000011bae000002001b6005821c201b321b940a921c4000011b4014e01c00020000070001000f164c1240000113a202001a200001000d0001000100010001001b0001000100010001000100010065000100010001000100010009000100010001000100010065000100010001000b00010065000100010017000100010005001900010015006500010d0000000d00000012005e00255a5652050064000763625c4e0000004b5b0000110000001f64622c1e58492c184643400f54002c2e3e002c123a002c0c36012c06302a2c003c38349048 else 0x180c1cc01d0417c01804180005e605ec05e005ee18101ccc1d1417c41d00000b014c05e2022005f201401ce0022015e0002b17d4002b0035002b002b000b000b002b1d0c17c8002b00000220002b17cc15ec18141d101808000b17d00220002b000b002b002b002b0091002b002b002b002b00990035002b000b002b000b0035002b002b1d080091002b000b002b002b002b000b002b008b002b002b002b002b002b000b002b002b0035002b002b007b002b002b002b002b002b13005800005b51003f000000120058000a004d0027005800220056001d0056000a564d2e1855402e3954002e1253162e064b36370049302e0e472d370045002e0c34002e8844) else (if i < 448 then 0x270025001d006d1d50001d001d01401a24000100031d440023001d0001001d001d1a20060c001d001f001d160002401d2000010606006f02401d400240002d160c1a34002f001d06001a2c001d002b06021ccc02401d480021001d001d0001014c0240001d06120001001d000d1a301d54001d001d060e1a280000001d1cc0001d1d4c001d001d001d0240024000290240001d44050003023001420c01044702013e4643012f03023f3a03023c380037052f002b0537050305251b03230e05010521091f05161a03003300180b2915321031052d8241 else 0x46002c004c002800400034004e00240042008c00a6003000ac00c8020001b4008e01a001a8021401a4005201240180020801f4020400200160018c010000e801e801c801e401cc00e000860126014c012001e0006600c0012a010a00e40104016c006c020c010600b200c402100140006000ae01ac01d4010801d001b000000072012801ec00a2009200a001f00240006e010201c000820122008001c4022000622c0000003e0000004100000026504f111f4e4d11184c4b11084a491100484511103b35113934291133201911582c)))))))))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 8
  | 8 => 179
  | 9 => 235
  | 10 => 19
  | 11 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 15
  | 9 => 194
  | 10 => 429
  | 11 => 448
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)
def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+16*((h/a+d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with
  | 1 => ws.map (blockWord 73 [1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9, 13, 12, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21])
  | 2 => ws.map (blockWord 73 [2, 3, 0, 1, 5, 4, 8, 9, 6, 7, 11, 10, 14, 15, 12, 13, 17, 16, 20, 21, 18, 19, 23, 22])
  | 3 => ws.map (blockWord 73 [3, 2, 5, 4, 0, 1, 9, 8, 11, 10, 6, 7, 15, 14, 17, 16, 12, 13, 21, 20, 23, 22, 18, 19])
  | 4 => ws.map (blockWord 73 [4, 5, 1, 0, 3, 2, 10, 11, 7, 6, 9, 8, 16, 17, 13, 12, 15, 14, 22, 23, 19, 18, 21, 20])
  | 5 => ws.map (blockWord 73 [5, 4, 3, 2, 1, 0, 11, 10, 9, 8, 7, 6, 17, 16, 15, 14, 13, 12, 23, 22, 21, 20, 19, 18])
  | 6 => ws.map (blockWord 73 [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17])
  | 7 => ws.map (blockWord 73 [7, 6, 10, 11, 8, 9, 1, 0, 4, 5, 2, 3, 19, 18, 22, 23, 20, 21, 13, 12, 16, 17, 14, 15])
  | 8 => ws.map (blockWord 73 [8, 9, 6, 7, 11, 10, 2, 3, 0, 1, 5, 4, 20, 21, 18, 19, 23, 22, 14, 15, 12, 13, 17, 16])
  | 9 => ws.map (blockWord 73 [9, 8, 11, 10, 6, 7, 3, 2, 5, 4, 0, 1, 21, 20, 23, 22, 18, 19, 15, 14, 17, 16, 12, 13])
  | 10 => ws.map (blockWord 73 [10, 11, 7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 22, 23, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14])
  | 11 => ws.map (blockWord 73 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12])
  | _ => ws

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 876) (goal 876) s ws) :
    NatRun (mask 876) (goal 876) s (rotateE g ws) := by
  unfold rotateE
  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 876 stateE nsE actionE sixE rotateE s

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h4y0 : span (Z 4) 1 0 = true := by decide +kernel

theorem z4 : span (Z 4) 1 0 = true := h4y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel

theorem z5 : span (Z 5) 1 0 = true := h5y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h6y0 : span (Z 6) 1 0 = true := by decide +kernel

theorem z6 : span (Z 6) 1 0 = true := h6y0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h7y0 : span (Z 7) 4 0 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h7y4 : span (Z 7) 4 4 = true := by decide +kernel

theorem z7 : span (Z 7) 8 0 = true := (@span_join (Z 7) 4 0 4 h7y0 h7y4)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y0 : span (Z 8) 4 0 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y4 : span (Z 8) 4 4 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y8 : span (Z 8) 4 8 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y12 : span (Z 8) 4 12 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y16 : span (Z 8) 4 16 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y20 : span (Z 8) 4 20 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y24 : span (Z 8) 4 24 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y28 : span (Z 8) 4 28 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y32 : span (Z 8) 4 32 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y36 : span (Z 8) 4 36 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y40 : span (Z 8) 4 40 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y44 : span (Z 8) 4 44 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y48 : span (Z 8) 4 48 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y52 : span (Z 8) 4 52 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y56 : span (Z 8) 4 56 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y60 : span (Z 8) 4 60 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y64 : span (Z 8) 4 64 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y68 : span (Z 8) 4 68 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y72 : span (Z 8) 4 72 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y76 : span (Z 8) 4 76 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y80 : span (Z 8) 4 80 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y84 : span (Z 8) 4 84 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y88 : span (Z 8) 4 88 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y92 : span (Z 8) 4 92 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y96 : span (Z 8) 4 96 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y100 : span (Z 8) 4 100 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y104 : span (Z 8) 4 104 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y108 : span (Z 8) 4 108 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y112 : span (Z 8) 4 112 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y116 : span (Z 8) 4 116 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y120 : span (Z 8) 4 120 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y124 : span (Z 8) 4 124 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y128 : span (Z 8) 4 128 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y132 : span (Z 8) 4 132 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y136 : span (Z 8) 4 136 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y140 : span (Z 8) 4 140 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y144 : span (Z 8) 4 144 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y148 : span (Z 8) 4 148 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y152 : span (Z 8) 4 152 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y156 : span (Z 8) 4 156 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y160 : span (Z 8) 4 160 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y164 : span (Z 8) 4 164 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y168 : span (Z 8) 4 168 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y172 : span (Z 8) 4 172 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h8y176 : span (Z 8) 3 176 = true := by decide +kernel

theorem z8 : span (Z 8) 179 0 = true := (@span_join (Z 8) 88 0 91 (@span_join (Z 8) 44 0 44 (@span_join (Z 8) 20 0 24 (@span_join (Z 8) 8 0 12 (@span_join (Z 8) 4 0 4 h8y0 h8y4) (@span_join (Z 8) 4 8 8 h8y8 (@span_join (Z 8) 4 12 4 h8y12 h8y16))) (@span_join (Z 8) 12 20 12 (@span_join (Z 8) 4 20 8 h8y20 (@span_join (Z 8) 4 24 4 h8y24 h8y28)) (@span_join (Z 8) 4 32 8 h8y32 (@span_join (Z 8) 4 36 4 h8y36 h8y40)))) (@span_join (Z 8) 20 44 24 (@span_join (Z 8) 8 44 12 (@span_join (Z 8) 4 44 4 h8y44 h8y48) (@span_join (Z 8) 4 52 8 h8y52 (@span_join (Z 8) 4 56 4 h8y56 h8y60))) (@span_join (Z 8) 12 64 12 (@span_join (Z 8) 4 64 8 h8y64 (@span_join (Z 8) 4 68 4 h8y68 h8y72)) (@span_join (Z 8) 4 76 8 h8y76 (@span_join (Z 8) 4 80 4 h8y80 h8y84))))) (@span_join (Z 8) 44 88 47 (@span_join (Z 8) 20 88 24 (@span_join (Z 8) 8 88 12 (@span_join (Z 8) 4 88 4 h8y88 h8y92) (@span_join (Z 8) 4 96 8 h8y96 (@span_join (Z 8) 4 100 4 h8y100 h8y104))) (@span_join (Z 8) 12 108 12 (@span_join (Z 8) 4 108 8 h8y108 (@span_join (Z 8) 4 112 4 h8y112 h8y116)) (@span_join (Z 8) 4 120 8 h8y120 (@span_join (Z 8) 4 124 4 h8y124 h8y128)))) (@span_join (Z 8) 24 132 23 (@span_join (Z 8) 12 132 12 (@span_join (Z 8) 4 132 8 h8y132 (@span_join (Z 8) 4 136 4 h8y136 h8y140)) (@span_join (Z 8) 4 144 8 h8y144 (@span_join (Z 8) 4 148 4 h8y148 h8y152))) (@span_join (Z 8) 12 156 11 (@span_join (Z 8) 4 156 8 h8y156 (@span_join (Z 8) 4 160 4 h8y160 h8y164)) (@span_join (Z 8) 4 168 7 h8y168 (@span_join (Z 8) 4 172 3 h8y172 h8y176))))))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y0 : span (Z 9) 4 0 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y4 : span (Z 9) 4 4 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y8 : span (Z 9) 4 8 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y12 : span (Z 9) 4 12 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y16 : span (Z 9) 4 16 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y20 : span (Z 9) 4 20 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y24 : span (Z 9) 4 24 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y28 : span (Z 9) 4 28 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y32 : span (Z 9) 4 32 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y36 : span (Z 9) 4 36 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y40 : span (Z 9) 4 40 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y44 : span (Z 9) 4 44 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y48 : span (Z 9) 4 48 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y52 : span (Z 9) 4 52 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y56 : span (Z 9) 4 56 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y60 : span (Z 9) 4 60 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y64 : span (Z 9) 4 64 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y68 : span (Z 9) 4 68 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y72 : span (Z 9) 4 72 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y76 : span (Z 9) 4 76 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y80 : span (Z 9) 4 80 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y84 : span (Z 9) 4 84 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y88 : span (Z 9) 4 88 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y92 : span (Z 9) 4 92 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y96 : span (Z 9) 4 96 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y100 : span (Z 9) 4 100 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y104 : span (Z 9) 4 104 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y108 : span (Z 9) 4 108 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y112 : span (Z 9) 4 112 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y116 : span (Z 9) 4 116 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y120 : span (Z 9) 4 120 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y124 : span (Z 9) 4 124 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y128 : span (Z 9) 4 128 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y132 : span (Z 9) 4 132 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y136 : span (Z 9) 4 136 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y140 : span (Z 9) 4 140 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y144 : span (Z 9) 4 144 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y148 : span (Z 9) 4 148 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y152 : span (Z 9) 4 152 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y156 : span (Z 9) 4 156 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y160 : span (Z 9) 4 160 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y164 : span (Z 9) 4 164 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y168 : span (Z 9) 4 168 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y172 : span (Z 9) 4 172 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y176 : span (Z 9) 4 176 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y180 : span (Z 9) 4 180 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y184 : span (Z 9) 4 184 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y188 : span (Z 9) 4 188 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y192 : span (Z 9) 4 192 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y196 : span (Z 9) 4 196 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y200 : span (Z 9) 4 200 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y204 : span (Z 9) 4 204 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y208 : span (Z 9) 4 208 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y212 : span (Z 9) 4 212 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y216 : span (Z 9) 4 216 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y220 : span (Z 9) 4 220 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y224 : span (Z 9) 4 224 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y228 : span (Z 9) 4 228 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h9y232 : span (Z 9) 3 232 = true := by decide +kernel

theorem z9 : span (Z 9) 235 0 = true := (@span_join (Z 9) 116 0 119 (@span_join (Z 9) 56 0 60 (@span_join (Z 9) 28 0 28 (@span_join (Z 9) 12 0 16 (@span_join (Z 9) 4 0 8 h9y0 (@span_join (Z 9) 4 4 4 h9y4 h9y8)) (@span_join (Z 9) 8 12 8 (@span_join (Z 9) 4 12 4 h9y12 h9y16) (@span_join (Z 9) 4 20 4 h9y20 h9y24))) (@span_join (Z 9) 12 28 16 (@span_join (Z 9) 4 28 8 h9y28 (@span_join (Z 9) 4 32 4 h9y32 h9y36)) (@span_join (Z 9) 8 40 8 (@span_join (Z 9) 4 40 4 h9y40 h9y44) (@span_join (Z 9) 4 48 4 h9y48 h9y52)))) (@span_join (Z 9) 28 56 32 (@span_join (Z 9) 12 56 16 (@span_join (Z 9) 4 56 8 h9y56 (@span_join (Z 9) 4 60 4 h9y60 h9y64)) (@span_join (Z 9) 8 68 8 (@span_join (Z 9) 4 68 4 h9y68 h9y72) (@span_join (Z 9) 4 76 4 h9y76 h9y80))) (@span_join (Z 9) 16 84 16 (@span_join (Z 9) 8 84 8 (@span_join (Z 9) 4 84 4 h9y84 h9y88) (@span_join (Z 9) 4 92 4 h9y92 h9y96)) (@span_join (Z 9) 8 100 8 (@span_join (Z 9) 4 100 4 h9y100 h9y104) (@span_join (Z 9) 4 108 4 h9y108 h9y112))))) (@span_join (Z 9) 60 116 59 (@span_join (Z 9) 28 116 32 (@span_join (Z 9) 12 116 16 (@span_join (Z 9) 4 116 8 h9y116 (@span_join (Z 9) 4 120 4 h9y120 h9y124)) (@span_join (Z 9) 8 128 8 (@span_join (Z 9) 4 128 4 h9y128 h9y132) (@span_join (Z 9) 4 136 4 h9y136 h9y140))) (@span_join (Z 9) 16 144 16 (@span_join (Z 9) 8 144 8 (@span_join (Z 9) 4 144 4 h9y144 h9y148) (@span_join (Z 9) 4 152 4 h9y152 h9y156)) (@span_join (Z 9) 8 160 8 (@span_join (Z 9) 4 160 4 h9y160 h9y164) (@span_join (Z 9) 4 168 4 h9y168 h9y172)))) (@span_join (Z 9) 28 176 31 (@span_join (Z 9) 12 176 16 (@span_join (Z 9) 4 176 8 h9y176 (@span_join (Z 9) 4 180 4 h9y180 h9y184)) (@span_join (Z 9) 8 188 8 (@span_join (Z 9) 4 188 4 h9y188 h9y192) (@span_join (Z 9) 4 196 4 h9y196 h9y200))) (@span_join (Z 9) 16 204 15 (@span_join (Z 9) 8 204 8 (@span_join (Z 9) 4 204 4 h9y204 h9y208) (@span_join (Z 9) 4 212 4 h9y212 h9y216)) (@span_join (Z 9) 8 220 7 (@span_join (Z 9) 4 220 4 h9y220 h9y224) (@span_join (Z 9) 4 228 3 h9y228 h9y232))))))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h10y0 : span (Z 10) 4 0 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h10y4 : span (Z 10) 4 4 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h10y8 : span (Z 10) 4 8 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h10y12 : span (Z 10) 4 12 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h10y16 : span (Z 10) 3 16 = true := by decide +kernel

theorem z10 : span (Z 10) 19 0 = true := (@span_join (Z 10) 8 0 11 (@span_join (Z 10) 4 0 4 h10y0 h10y4) (@span_join (Z 10) 4 8 7 h10y8 (@span_join (Z 10) 4 12 3 h10y12 h10y16)))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem h11y0 : span (Z 11) 1 0 = true := by decide +kernel

theorem z11 : span (Z 11) 1 0 = true := h11y0

theorem checkedE (s : Nat) (hs : s ≤ 11) : ∀ i < nsE s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 876) (goal 876) s xs516) : False := by
  have h11 : NatRun (mask 876) (goal 876) 11 xs516 := extend_run h hs
  have p : xs516.Perm (stateE 11 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 11 (by decide) 0 (by decide) (Run.perm p h11)
end Theta516

theorem PEqualNP.Outside.L_meta_516 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := Theta516.main516 Theta516.noRunFull
