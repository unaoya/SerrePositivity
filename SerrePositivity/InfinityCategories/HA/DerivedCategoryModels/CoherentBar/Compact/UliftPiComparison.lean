module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPointedFilling
/-!
概要：指定基点での正次数 π は追加の宇宙持ち上げで変わらない。
方針：同じ球面代表と充填の上下操作を商へ降ろし、積の充填も保持する。
規約：追加宇宙は任意で、元の頂点と元の代表を使う。
使われ方：持ち上げた native 評価空間の π チャートを、元の評価空間へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (X : SSet.{u}) [KanComplex X] (n : ℕ) (x : X _⦋0⦌)

def dgBarCompactPiUliftUp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x →
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) :=
  Quotient.map _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp (by
    intro f g h
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (X := X) 0).mp h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (X := (SSet.uliftFunctor.{v, u}).obj X) 0).mpr
      ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedRelUp r⟩)

def dgBarCompactPiUliftDown :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x :=
  Quotient.map _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexDown (by
    intro f g h
    obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (X := (SSet.uliftFunctor.{v, u}).obj X) 0).mp h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (X := X) 0).mpr ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedRelDown r⟩)

/-- 元の代表を保つ、任意追加宇宙での全基点 π 群同型。 -/
def dgBarCompactUliftPiEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x ≃*
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((SSet.uliftFunctor.{v, u}).obj X) n (ULift.up x) where
  toFun := dgBarCompactPiUliftUp X n x
  invFun := dgBarCompactPiUliftDown X n x
  left_inv a := by
    induction a using Quotient.inductionOn with | h f => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexDown
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v} f)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPointedSimplexEquiv X (n + 1) x).left_inv f)
  right_inv a := by
    induction a using Quotient.inductionOn with | h f => ?_
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexUp.{u, v}
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedSimplexDown f)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPointedSimplexEquiv X (n + 1) x).right_inv f)
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h f => ?_
    induction b using Quotient.inductionOn with | h g => ?_
    obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.productSimplex_spec f g
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPointedMulUp.{u, v} r)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
