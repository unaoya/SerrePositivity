module

public import SerrePositivity.InfinityCategories.F2.FunctorSquareValueProjectionTo
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionTotal

/-!
概要：元の二面比較を、指定された native 頂点の同じ値空間へ全係数で射影する。
方針：元の比較を元の頂点等式による射影で写し、同じ native な比較へ照合する。
規約：元の対角・二面・指定値を保持。使われ方：五因子の左辺と a6 の作用比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {C : SSet.{u + 1}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
  (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
  (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌)

/-- 元の二面比較の指定値を、同じ頂点等式で固定した値空間へ射影した全係数の比較。 -/
def coherentColimitUnitValueActionTo :=
  VertexIso.map (coherentColimitUnitValueComparison B H p x)
    (constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex G))

/-- 固定値への元の二面比較は、同じ native 表示の二面比較の元の値を保持する。 -/
lemma coherentColimitUnitValueActionTo_heq_native :
    HEq (coherentColimitUnitValueActionTo B H p x)
      (VertexIso.map (coherentColimitNativeUnitValueComparison B H p x)
        ((constantUnstraighteningRelativeIso p (coherentDiagramTotalVertex G)).hom ≫
          (ihom C).map (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)) :=
  functorSquareComparison_projectionTo_heq
    (coherentColimitUnitUpperTriangle B H) (coherentColimitUnitLowerTriangle B H)
    (coherentColimitNativeUnitFunctorTriangle B H) (coherentColimitTargetLowerTriangle B H)
    (coherentDiagramTotalCocone_vertex G) (coherentNativeUnitHomotopy_h G).symm
    rfl rfl rfl rfl p x

omit p x in
/-- 元の恒等初期値で射影した比較は、a6 と同じ native 中央比較の指定値に一致する。 -/
lemma coherentColimitUnitValueActionTo_total_heq_native :
    HEq (coherentColimitUnitValueActionTo B H (leftUnstraighteningProjection F)
      (relativeFunctorVertex (leftUnstraighteningProjection F) (leftUnstraighteningProjection F)
        (𝟙 (leftUnstraightening F)) (Category.id_comp _)))
      (coherentColimitNativeTriangleActionComparison B H) := by
  let p₀ := leftUnstraighteningProjection F
  let x₀ := relativeFunctorVertex p₀ p₀ (𝟙 (leftUnstraightening F)) (Category.id_comp p₀)
  refine (coherentColimitUnitValueActionTo_heq_native B H p₀ x₀).trans ?_
  refine (functorSquareComparison_total_app_map_heq
    (coherentColimitNativeUnitFunctorTriangle B H) (coherentColimitTargetLowerTriangle B H)
    ((constantUnstraighteningRelativeIso p₀ (coherentDiagramTotalVertex G)).hom ≫
      (ihom (leftUnstraightening F)).map
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)).trans ?_
  exact (coherentColimitNativeUnitRelativeComparison_map_heq_action B H).trans
    (coherentColimitNativeTriangleActionComparison_heq_original B H).symm

end SerrePositivity.InfinityCategories.F2
