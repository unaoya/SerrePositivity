module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundarySimplices

/-! # 左右の単体を貼り合わせた join の充填

概要：共通面で一致する左右の実際の単体を標準 span の join 上の一つの写像へ貼る。
方針：二セル表示の押し出しの普遍性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：coslice の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：左右の単体を表す写像は押し出しの共通面で一致する。
方針：面の Yoneda 公式で単体の共通面の等式へ戻す。
規約：HTT §1.2.13。使われ方：join の二セルの貼合せの整合条件。 -/
lemma dgModuleConeBoundaryCells_compatible {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)) ≫
        (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftSimplex A D f b hb) :
          (Δ[n + 3] : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) =
      SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightSimplex A D f b hb) := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  congr 1
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundarySimplex_common A D f b hb

/-- 概要：左右の単体を標準 span の join 上の一写像に貼り合わせる。
方針：二つの標準セルの押し出しに、共通面で一致する二写像を与える。
規約：HTT §1.2.13。使われ方：実際の slice の充填写像の uncurry。 -/
def dgModuleConeBoundaryJoinFiller {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet) Δ[n + 1] ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout (n + 1)).desc
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftSimplex A D f b hb))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightSimplex A D f b hb))
    (dgModuleConeBoundaryCells_compatible A D f b hb)

/-- 概要：貼合せた充填の左セルへの制限は構成した左単体。
方針：押し出しの降下の第一の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の左の既知面との比較。 -/
lemma dgModuleConeBoundaryJoinFiller_left {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft (n + 1) ≫ dgModuleConeBoundaryJoinFiller A D f b hb =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLeftSimplex A D f b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout (n + 1)).inl_desc _ _ _

/-- 概要：貼合せた充填の右セルへの制限は構成した右単体。
方針：押し出しの降下の第二の制限公式を使う。
規約：HTT §1.2.13。使われ方：元の境界の右の既知面との比較。 -/
lemma dgModuleConeBoundaryJoinFiller_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight (n + 1) ≫ dgModuleConeBoundaryJoinFiller A D f b hb =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightSimplex A D f b hb) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout (n + 1)).inr_desc _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
