module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornLastCutIndices
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralCochains
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! # 一般最上位 rhs の最後の一寄与の符号と合成

概要：最後内部頂点の寄与は、削除成分の負と最後辺による欠面成分の後合成の和。
方針：二つの切断成分の次数を異種等号で正規化し、上側の一点から符号 −1 を得る。
規約：元の rhs の符号を保持。使われ方：Q 挿入による一般最上位 rhs の分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (s : SimplexData A D (n + 2))

/-- 最上位 A の微分右辺を、同じ固定端点・次数で読む。 -/
def dgLastHornTopRhs :=
  s.rhs Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)

/-- 同じ最上位右辺の最後内部頂点の寄与。 -/
def dgLastHornLastTerm :=
  s.term Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)
    (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_pos n)
    (dgLastHornPenultimate_lt_last n)

/-- 最後内部頂点を消した、同じ最上位微分右辺の次数の成分。 -/
def dgLastHornLastErased :=
  s.erasedComponent Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
    (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)
    (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_pos n)
    (dgLastHornPenultimate_lt_last n)

/-- 最後辺と欠面の最上位成分の、同じ rhs 次数への後合成。 -/
def dgLastHornLastComposite :
    GradedHom A (s.obj 0) (s.obj (Fin.last (n + 2))) (-(n : ℤ) - 1 + 1) :=
  compose A (s.edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
    (dgLastHornPenultimate_lt_last n))
    (s.hom (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
      (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)) (by omega)

/-- 最後内部頂点の二つの切断合成は、最後辺と欠面成分の同じ後合成。 -/
lemma dgLastHornLastCut_composite :
    s.cutComposite Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (dgLastHornTop_two n)
      (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)
      (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_pos n)
      (dgLastHornPenultimate_lt_last n) = dgLastHornLastComposite s := by
  have hlk : 2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (· ≤ dgLastHornPenultimate n)).card : ℤ) = -(n : ℤ) := by
    rw [dgLastHornLastCut_left, dgLastHornMissingIndex_card]
    push_cast
    ring
  have hrk : 2 - (((Finset.univ : Finset (Fin (n + 3))).filter
      (dgLastHornPenultimate n ≤ ·)).card : ℤ) = 0 := by
    rw [dgLastHornLastCut_right]
    simp [dgLastHornPenultimate, Fin.castSucc_ne_last]
  have hl : HEq (s.cutLeft Finset.univ 0 (dgLastHornTop_two n) (dgLastHornTop_min n)
      (dgLastHornPenultimate n) (Finset.mem_univ _) (dgLastHornPenultimate_pos n))
      (s.hom (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
        (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
        (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)) := by
    exact s.hom_heq_of_indices_degree (dgLastHornLastCut_left n) rfl rfl hlk
  have hr : HEq (s.cutRight Finset.univ (Fin.last (n + 2)) (dgLastHornTop_two n)
      (dgLastHornTop_max n) (dgLastHornPenultimate n) (Finset.mem_univ _)
      (dgLastHornPenultimate_lt_last n))
      (s.edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
        (dgLastHornPenultimate_lt_last n)) := by
    exact s.hom_heq_of_indices_degree (dgLastHornLastCut_right n) rfl rfl hrk
  exact eq_of_heq (gradedHom_compose_heq rfl rfl rfl hlk hrk rfl _ _ _ _ hr hl
    (by rw [hlk, hrk]; omega) (by omega))

/-- 最後の符号付き寄与は、削除成分の負と同じ最後辺の後合成との和。 -/
lemma dgLastHornLastTerm_formula :
    dgLastHornLastTerm s = -dgLastHornLastErased s + dgLastHornLastComposite s := by
  unfold dgLastHornLastTerm
  rw [SimplexData.term_eq_sub_cutComposite, dgLastHornLastCut_upper_card,
    dgLastHornLastCut_composite]
  change (-1 : ℤ) • (dgLastHornLastErased s - dgLastHornLastComposite s) = _
  simp only [neg_smul, one_smul]
  abel

end SerrePositivity.InfinityCategories
