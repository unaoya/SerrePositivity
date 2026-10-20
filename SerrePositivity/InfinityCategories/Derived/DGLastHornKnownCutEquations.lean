module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornOtherCutIndices
public import SerrePositivity.InfinityCategories.Derived.DGLastHornTopRhsDifference

/-! # 一般最後外ホーンの切断集合の既知方程式

概要：内部頂点の左右切断・削除集合に、欠面以外の既知方程式を供給する。
方針：全体集合と欠面でないことを有限集合の補題から渡す。
規約：左切断だけは最後内部頂点を除く。使われ方：Bianchi の寄与の一般消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 欠面と最上位以外の回収データの全端点・全次数の方程式。 -/
lemma dgGeneralLastHornKnown_equation (I : Finset (Fin (n + 3)))
    (hf : I ≠ Finset.univ) (hm : I ≠ dgLastHornMissingIndex n) :
    (HornData.knownData σ).Equation I :=
  fun a b k hI ha hb hk => HornData.knownData_equation σ I a b k hI ha hb hk hf hm

/-- 最後以外の内部頂点への左切断は既知方程式を満たす。 -/
lemma dgGeneralLastHornKnown_leftCut (j : Fin (n + 3)) (hj : j < Fin.last (n + 2))
    (hne : j ≠ dgLastHornPenultimate n) :
    (HornData.knownData σ).Equation (Finset.univ.filter (· ≤ j)) :=
  dgGeneralLastHornKnown_equation σ _ (dgLastHornLeftCut_ne_univ j hj)
    (dgLastHornLeftCut_ne_missing j hne)

/-- 任意の内部頂点からの右切断は既知方程式を満たす。 -/
lemma dgGeneralLastHornKnown_rightCut (j : Fin (n + 3))
    (h₀ : (0 : Fin (n + 3)) < j) (hj : j < Fin.last (n + 2)) :
    (HornData.knownData σ).Equation (Finset.univ.filter (j ≤ ·)) :=
  dgGeneralLastHornKnown_equation σ _ (dgLastHornRightCut_ne_univ j h₀)
    (dgLastHornRightCut_ne_missing j hj)

/-- 任意の内部頂点削除も既知方程式を満たす。 -/
lemma dgGeneralLastHornKnown_erase (j : Fin (n + 3)) (hj : j < Fin.last (n + 2)) :
    (HornData.knownData σ).Equation (Finset.univ.erase j) :=
  dgGeneralLastHornKnown_equation σ _ (dgLastHornErase_ne_univ j)
    (dgLastHornErase_ne_missing j hj)

end SerrePositivity.InfinityCategories
