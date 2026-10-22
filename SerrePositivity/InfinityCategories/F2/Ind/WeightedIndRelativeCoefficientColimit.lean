module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeCoefficientClass
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationIsoColimit
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeImageColimit

/-!
概要：同じ相対 join の全単位の係数制限も、元の指定密度単位と同じ余極限性を持つ。
方針：同じ係数変換空間内の同型を、native 余錐比較の充満忠実性で戻す。
規約：元の全単位の同じ制限を保持。使われ方：相対 join の fiber 余錐の局所普遍性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I)
local notation "D" => weightedIndCoefficientDiagram κ F i
local notation "z" => weightedIndCoefficientVertex κ F hF i

/-- 同じ相対 join の全単位の係数制限を実現する、同じ両端固定の native 余錐データ。 -/
def weightedIndRelativeCoefficientRealization :=
  F2.homotopyCoconeRealization (weightedIndRelativeCoefficientHomotopy κ F hF i)

/-- 同じ相対 join の全単位から得た、元の係数図式上の native 余錐。 -/
def weightedIndRelativeCoefficientCocone : JoinCocone D :=
  (weightedIndRelativeCoefficientRealization κ F hF i).cocone

lemma weightedIndRelativeCoefficientCocone_vertex :
    (weightedIndRelativeCoefficientCocone κ F hF i).vertex = z :=
  (weightedIndRelativeCoefficientRealization κ F hF i).vertex_eq

/-- 元の指定係数余錐と同じ相対 join 単位の係数余錐は、同じ標準変換空間内で同型。 -/
def weightedIndRelativeCoefficientCoconeTransformationIso : VertexIso
    ((F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (weightedIndDensityCoefficientCocone κ F hF i) z
        (weightedIndDensityCoefficientCocone_vertex κ F hF i)))
    ((F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (weightedIndRelativeCoefficientCocone κ F hF i) z
        (weightedIndRelativeCoefficientCocone_vertex κ F hF i))) :=
  weightedCoefficientCoconeTransformationIso κ F hF i ≪≫
    (weightedIndRelativeCoefficientTransformationIso κ F hF i).symm ≪≫
      (homotopyCoconeTransformationIso (weightedIndRelativeCoefficientHomotopy κ F hF i)
        (weightedIndRelativeCoefficientRealization κ F hF i)).symm

/-- 元の相対 join 単位の同じ係数制限から実現した余錐は、同じ係数図式の余極限。 -/
lemma weightedIndRelativeCoefficientCocone_isColimit :
    IsColimitCone (weightedIndRelativeCoefficientCocone κ F hF i) :=
  isColimitCone_of_coconeTransformationIso _ _ z
    (weightedIndDensityCoefficientCocone_vertex κ F hF i)
    (weightedIndRelativeCoefficientCocone_vertex κ F hF i)
    (weightedIndRelativeCoefficientCoconeTransformationIso κ F hF i)
    (weightedIndDensityCoefficientCocone_isColimit κ F hF i)

/-- 元の相対 join 単位の同じ係数余錐の左 Kan 像も、同じ像の図式の余極限。 -/
lemma weightedIndRelativeCoefficientCocone_image_isColimit
    [IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    IsColimitCone (mapJoinCocone G (weightedIndRelativeCoefficientCocone κ F hF i)) := by
  let c := weightedIndDensityCoefficientCocone κ F hF i
  let d := weightedIndRelativeCoefficientCocone κ F hF i
  have hGc : IsColimitCone (mapJoinCocone G c) :=
    weightedIndDensityCoefficientCocone_image_isColimit κ F hF i β hβ
  exact hGc.of_functorIso ((coconeFunctorIsoOfVertexIso c d (colimitConeIso c d
    (weightedIndDensityCoefficientCocone_isColimit κ F hF i)
    (weightedIndRelativeCoefficientCocone_isColimit κ F hF i))).postcomp G)

end SerrePositivity.InfinityCategories.F2.Ind
