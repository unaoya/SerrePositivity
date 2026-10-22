module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleSourceValue
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionCoherence

/-!
概要：元の値の整合式の定値余極限三角形因子を、同じ単位での前合成へ戻す。
方針：元の余錐単位の実射と相対頂点を照合し、任意始点の値の比較を適用する。
規約：元の三角形・単位円柱・指定比較を保持。使われ方：下側の輸送因子の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "p" => leftUnstraighteningProjection F
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "u₀" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "v₀" => leftUnstraighteningMappingVertexMap F (SSet.const z₀)
  (coherentVertexOfHomotopy u₀)
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z₃) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F))
    (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z₃))

/-- 元の定値余極限三角形の指定因子は、同じ全空間比較を元の単位で前合成した値。 -/
lemma coherentColimitConstantTriangleValue_heq_total :
    HEq (VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
        ((functorHomotopyRelativePost u₀ p).app _ x₀)) Q)
      ((functorTriangleConstantTargetActionIso (coherentColimitConstantTriangle B T)).precomp
        (Subtype.val v₀)) := by
  have hx : (functorHomotopyRelativePost u₀ p).app _ x₀ =
      relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z₀)) p
        (Subtype.val v₀) (Subtype.property v₀) := by
    apply Subtype.ext
    rfl
  rw [hx]
  exact functorTriangleSequentialPostComparison_source_value_heq_over_base
    (coherentColimitConstantTriangle B T) (Subtype.val v₀) p (Subtype.property v₀)

end SerrePositivity.InfinityCategories.F2
