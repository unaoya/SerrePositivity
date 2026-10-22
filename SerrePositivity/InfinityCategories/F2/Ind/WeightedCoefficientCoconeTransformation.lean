module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientDiagramVertex
public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyCoconeTransformationIso
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPost

/-!
概要：同じ指定係数余錐とその評価の標準変換を、元の全変換の同じ係数制限へ比較する。
方針：元の余錐実現の両端固定比較と、標準変換の後合成自然性を使う。
規約：指定 native 余錐を保持。使われ方：実際の評価 fiber 写像の余極限判定。
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

/-- 元の共同分類の同じ添字における、指定係数余錐の頂点。 -/
abbrev weightedIndCoefficientVertex :=
  (weightedIndClassification κ F hF).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i))

/-- 元の係数全空間上の同じ表現可能図式。 -/
abbrev weightedIndCoefficientDiagram :=
  (SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫ indYoneda κ C
local notation "D" => weightedIndCoefficientDiagram κ F i
local notation "z" => weightedIndCoefficientVertex κ F hF i

/-- 指定 native 係数余錐の標準変換は、元の全変換の同じ係数制限と同型。 -/
def weightedCoefficientCoconeTransformationIso :
    VertexIso ((F2.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (weightedIndDensityCoefficientCocone κ F hF i) z
        (weightedIndDensityCoefficientCocone_vertex κ F hF i)))
      (homotopyTransformationVertex (weightedIndDensityCoefficientHomotopy κ F hF i)) :=
  homotopyCoconeTransformationIso (weightedIndDensityCoefficientHomotopy κ F hF i)
    (weightedIndDensityCoefficientRealization κ F hF i)

/-- 同じ係数余錐を任意の関手で評価した標準変換も、元の指定変換の同じ像と同型。 -/
def weightedCoefficientCoconePostTransformationIso {X : SSet.{u + 1}}
    (q : IndInfinity κ C ⟶ X) :
    VertexIso ((F2.coconeTransformationMap (D ≫ q) (q.app (Opposite.op ⦋0⦌) z)).app
      (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (mapJoinCocone q (weightedIndDensityCoefficientCocone κ F hF i))
        (q.app (Opposite.op ⦋0⦌) z) (by
          rw [mapJoinCocone_vertex, weightedIndDensityCoefficientCocone_vertex])))
      ((F2.constantTransformationPost D z q).app (Opposite.op ⦋0⦌)
        (homotopyTransformationVertex (weightedIndDensityCoefficientHomotopy κ F hF i))) := by
  have hn := coconeTransformationPointAt_post (weightedIndDensityCoefficientCocone κ F hF i)
    z (weightedIndDensityCoefficientCocone_vertex κ F hF i) q (by
      rw [mapJoinCocone_vertex, weightedIndDensityCoefficientCocone_vertex])
  exact eqToIso (congrArg HomotopyCategory.mk hn.symm) ≪≫
    (weightedCoefficientCoconeTransformationIso κ F hF i).map (F2.constantTransformationPost D z q)

end SerrePositivity.InfinityCategories.F2.Ind
