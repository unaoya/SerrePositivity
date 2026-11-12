module
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
概要：上界を持つ poset の単体へ、その上界を最後の頂点として付加する。
方針：元の頂点を保つ単調写像を作り、非退化性と最後の退化の場合を判定する。
規約：単体ラベルとその face を保持する。
使われ方：filtered strict bar の局所縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {J : Type u} [PartialOrder J] {n : ℕ}

def dgStrictAppendOrder (s : (nerve J) _⦋n⦌) (b : J) (hb : s.obj (Fin.last n) ≤ b) :
    Fin (n + 2) →o J where
  toFun i := if h : i.val < n + 1 then s.obj ⟨i.val, h⟩ else b
  monotone' := by
    intro i j hij
    dsimp
    split_ifs with hi hj hj
    · exact s.monotone (by exact hij)
    · exact (s.monotone (Fin.le_last _)).trans hb
    · exact False.elim (hi (lt_of_le_of_lt hij hj))
    · exact le_rfl

def dgStrictAppendSimplex (s : (nerve J) _⦋n⦌) (b : J) (hb : s.obj (Fin.last n) ≤ b) :
    (nerve J) _⦋n + 1⦌ := (dgStrictAppendOrder s b hb).monotone.functor

@[simp] lemma dgStrictAppendSimplex_obj_castSucc (s : (nerve J) _⦋n⦌)
    (b : J) (hb : s.obj (Fin.last n) ≤ b) (i : Fin (n + 1)) :
    (dgStrictAppendSimplex s b hb).obj i.castSucc = s.obj i := by
  simp only [dgStrictAppendSimplex, Monotone.functor_obj, dgStrictAppendOrder,
    OrderHom.coe_mk, Fin.coe_castSucc, dite_eq_left i.isLt]

@[simp] lemma dgStrictAppendSimplex_obj_last (s : (nerve J) _⦋n⦌)
    (b : J) (hb : s.obj (Fin.last n) ≤ b) :
    (dgStrictAppendSimplex s b hb).obj (Fin.last (n + 1)) = b := by
  simp only [dgStrictAppendSimplex, Monotone.functor_obj, dgStrictAppendOrder,
    OrderHom.coe_mk, Fin.val_last, lt_self_iff_false, dite_false]

lemma dgStrictAppendSimplex_face_last (s : (nerve J) _⦋n⦌)
    (b : J) (hb : s.obj (Fin.last n) ≤ b) :
    (nerve J).δ (Fin.last (n + 1)) (dgStrictAppendSimplex s b hb) = s := by
  ext i
  simp only [nerve.δ_obj, Fin.succAbove_last, dgStrictAppendSimplex_obj_castSucc]

lemma dgStrictAppendSimplex_degenerate_of_last_eq (s : (nerve J) _⦋n⦌)
    (b : J) (hb : s.obj (Fin.last n) ≤ b) (he : s.obj (Fin.last n) = b) :
    dgStrictAppendSimplex s b hb ∈ (nerve J).degenerate (n + 1) := by
  apply PartialOrder.mem_nerve_degenerate_of_eq (i := Fin.last n)
  simpa only [dgStrictAppendSimplex_obj_castSucc, Fin.succ_last,
    dgStrictAppendSimplex_obj_last] using he

lemma dgStrictAppendSimplex_nonDegenerate (s : (nerve J) _⦋n⦌)
    (hs : s ∈ (nerve J).nonDegenerate n) (b : J) (hb : s.obj (Fin.last n) < b) :
    dgStrictAppendSimplex s b hb.le ∈ (nerve J).nonDegenerate (n + 1) := by
  apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
  have hstrict := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs
  intro i j hij
  change (if h : i.val < n + 1 then s.obj ⟨i.val, h⟩ else b) <
    (if h : j.val < n + 1 then s.obj ⟨j.val, h⟩ else b)
  split_ifs with hi hj hj
  · exact hstrict (by exact hij)
  · exact lt_of_le_of_lt (s.monotone (Fin.le_last _)) hb
  · exact False.elim (hi (lt_trans hij hj))
  · have hi' := i.isLt
    have hj' := j.isLt
    change i.val < n + 2 at hi'
    change j.val < n + 2 at hj'
    have hij' : i.val < j.val := hij
    omega

lemma dgStrictFace_bound (s : (nerve J) _⦋n + 1⦌) (b : J)
    (hb : s.obj (Fin.last (n + 1)) ≤ b) (i : Fin (n + 2)) :
    ((nerve J).δ i s).obj (Fin.last n) ≤ b := by
  rw [nerve.δ_obj]
  exact (s.monotone (Fin.le_last _)).trans hb

lemma dgStrictAppendSimplex_face_castSucc (s : (nerve J) _⦋n + 1⦌) (b : J)
    (hb : s.obj (Fin.last (n + 1)) ≤ b) (i : Fin (n + 2)) :
    (nerve J).δ i.castSucc (dgStrictAppendSimplex s b hb) =
      dgStrictAppendSimplex ((nerve J).δ i s) b (dgStrictFace_bound s b hb i) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [nerve.δ_obj, Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i),
      dgStrictAppendSimplex_obj_last]
  · simp only [nerve.δ_obj, Fin.castSucc_succAbove_castSucc,
      dgStrictAppendSimplex_obj_castSucc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
