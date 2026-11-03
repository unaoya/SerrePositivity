module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedParameterGraphIso
public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductScaffoldValue
public import SerrePositivity.InfinityCategories.F1.Ind.VertexFiberIsoProjection

/-!
概要：元の係数の指定 fiber と、同じ共同 weighted 射影の初頂点引き戻しの fiber を底上で同定する。
方針：元のグラフ同型・二つの引き戻し同型・同じ底の頂点の等式を合成する。
規約：元の共同全空間への射を保持し、比較の全空間を変更しない。
使われ方：元の section product scaffold の fiber 同値性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 元の添字の積の頂点の像は、同じ単体の初頂点と同じ添字のグラフ上の点。 -/
lemma sectionProductBaseMap_vertex (i : I) (s : TransportSimplexCategory B) :
    (sectionProductBaseMap I B).app (Opposite.op ⦋0⦌) (nerveVertex (i, s)) =
      (underSectionFiberBase B i).app _
        ((SSet.yonedaEquiv.symm s.objDown.val).app _ (stdSimplex.obj₀Equiv.symm 0)) := by
  apply Prod.ext
  · rfl
  · exact (PinchedHom.constant_zero (nerveVertex i)).symm

/-- 元の係数の初頂点 fiber と、同じ初頂点引き戻しの元の fiber の同型。 -/
def sectionProductCoefficientFiberIso (i : I) (s : TransportSimplexCategory B) :
    vertexFiber (F.obj i).val.hom
      ((SSet.yonedaEquiv.symm s.objDown.val).app _ (stdSimplex.obj₀Equiv.symm 0)) ≅
    vertexFiber (pullback.snd (leftFibrationWeightedProjection F) (sectionProductBaseMap I B))
      (nerveVertex (i, s)) :=
  vertexFiberIsoOfTotalIso (F.obj i).val.hom
    (pullback.snd (leftFibrationWeightedProjection F) (underSectionFiberBase B i))
    (weightedParameterGraphIso (leftFibrationDiagramProjection F) i)
    (weightedParameterGraphIso_snd (leftFibrationDiagramProjection F) i) _ ≪≫
  vertexFiberPullbackIso (leftFibrationWeightedProjection F) (underSectionFiberBase B i) _ ≪≫
  eqToIso (congrArg (vertexFiber (leftFibrationWeightedProjection F))
    (sectionProductBaseMap_vertex i s).symm) ≪≫
  (vertexFiberPullbackIso (leftFibrationWeightedProjection F) (sectionProductBaseMap I B)
    (nerveVertex (i, s))).symm

/-- 同じ fiber 同型の全空間への射は、元の係数の fiber 包含と元の定値包含の合成。 -/
lemma sectionProductCoefficientFiberIso_total (i : I) (s : TransportSimplexCategory B) :
    (sectionProductCoefficientFiberIso F i s).hom ≫ vertexFiberι _ _ ≫ pullback.fst _ _ =
      vertexFiberι (F.obj i).val.hom _ ≫ weightedNerveConstantLift (leftFibrationTotalDiagram F) i := by
  simp only [sectionProductCoefficientFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [vertexFiberPullbackIso_inv_ι_fst,
    vertexFiber_vertexEqToIso_ι (leftFibrationWeightedProjection F)
      (sectionProductBaseMap_vertex i s).symm,
    vertexFiberPullbackIso_hom_ι, ← Category.assoc, vertexFiberIsoOfTotalIso_hom_ι,
    Category.assoc]
  exact congrArg (fun f ↦ vertexFiberι (F.obj i).val.hom
    ((SSet.yonedaEquiv.symm s.objDown.val).app _ (stdSimplex.obj₀Equiv.symm 0)) ≫ f)
    (weightedParameterGraphIso_fst (leftFibrationDiagramProjection F) i)

end SerrePositivity.InfinityCategories.F2.Ind
