module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCoslicePostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetUnit
/-!
概要：元の同じ Hom(x,x) 単位から、Hom の実 coslice 全体を比較する。
方針：同じ dg 左表現可能関手の後合成と、Yoneda 単位の閉始点前合成を接続する。
規約：共通対象宇宙で扱い、入力の小ささを仮定しない。
使われ方：D(R) 値 Hom と F1 の空間値 Hom の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x : C)
/-- 対象だけを共通宇宙へ持ち上げた、同じ実 Hom 加群値 dg 関手。 -/
def dgHomTargetModuleLift :
    DGFunctor R C (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1})) :=
  (dgHomTargetModuleDG R C x).comp
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
/-- 同じ Hom 単位から構成した、元の実 coslice 全体の比較射。 -/
def dgHomTargetCosliceComparison :
    dgVertexCoslice R C x ⟶ dgVertexCoslice R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (dgHomModuleUnit R C) :=
  dgFunctorCoslicePostcomp R (dgHomTargetModuleLift R C x) x ≫
    dgCoslicePrecompose R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      ((dgHomTargetModuleLift R C x).obj x) (dgHomModuleUnit R C)
      ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
        (dgHomTargetUnit R C x))
/-- 同じ全比較射は、元の実 Hom 関手を底に持つ。 -/
lemma dgHomTargetCosliceComparison_projection :
    dgHomTargetCosliceComparison R C x ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R C)) =
    sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x)) ≫
      dgNerve.map (dgHomTargetModuleLift R C x) := by
  rw [dgHomTargetCosliceComparison, Category.assoc, dgCoslicePrecompose_projection,
    dgFunctorCoslicePostcomp_projection]
end SerrePositivity.InfinityCategories
