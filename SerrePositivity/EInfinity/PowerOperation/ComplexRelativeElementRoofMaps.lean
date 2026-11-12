module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementIndexComparison
public import SerrePositivity.EInfinity.Hammock.AsSmallComparison
public import SerrePositivity.EInfinity.Hammock.LeftRoofSameUniverseComparison

/-!
# 元の相対全要素屋根の同じ正規化屋根への厳密な像

DAG XIII §2.2 の native な降下への前段。全語の AsSmall 比較と同じ要素の表示変更
だけを使い、指定した二つの脚・全縦射を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A] (X Y : Complex A)

def complexRelativeElementRoof :=
  LeftRoof.diagram (complexRelativeCategory A).weakEquivalences
    (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
    (complexRelativeElementAugmentation_weak A X Y) (complexRelativeElementEvaluation A X Y)
    (fun f => complexRelativeElementColumn_map_weak A X Y f)

def complexRelativeElementRoofMap :=
  LeftRoof.Precompose.SameUniverse.diagramColimitMap (complexRelativeCategory A).weakEquivalences
    (complexRelativeElementRoof A X Y)

lemma complexRelativeElementRoof_graph_image :
    let := projectiveModelCategory A
    let QX := (framedLimitProbeFunctor A).obj X
    LeftRoof.Precompose.SameUniverse.diagramGraphMap (complexRelativeCategory A).weakEquivalences
        (complexRelativeElementRoof A QX Y) ≫
      (AsSmallComparison.graphIso (weakEquivalences (Complex A)) QX Y LeftRoof.word).inv =
    (complexRelativeElementIndexIso A X Y).hom ≫
      FrameHom.frameLeftRoofNerveMap (Y := Y) (weakEquivalences (Complex A))
        ((normalizedProbeTensorFrame A).obj X) ((normalizedProbeTensorAugmentation A).app X)
        (normalizedProbeTensorAugmentation_weak A X)
        (fun f => normalizedSimplexTensor_homotopicallyConstant A
          ((framedLimitProbeFunctor A).obj X) f) := by
  let := projectiveModelCategory A
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let F := ((LeftRoof.Precompose.SameUniverse.diagramGraphMap
    (complexRelativeCategory A).weakEquivalences
      (complexRelativeElementRoof A ((framedLimitProbeFunctor A).obj X) Y) ≫
    (AsSmallComparison.graphIso (weakEquivalences (Complex A))
      ((framedLimitProbeFunctor A).obj X) Y LeftRoof.word).inv).app n) σ
  let G := (((complexRelativeElementIndexIso A X Y).hom ≫
    FrameHom.frameLeftRoofNerveMap (Y := Y) (weakEquivalences (Complex A))
      ((normalizedProbeTensorFrame A).obj X) ((normalizedProbeTensorAugmentation A).app X)
      (normalizedProbeTensorAugmentation_weak A X)
      (fun f => normalizedSimplexTensor_homotopicallyConstant A
        ((framedLimitProbeFunctor A).obj X) f)).app n) σ
  have ho (i : Fin (n.unop.len + 1)) : F.obj i = G.obj i := by
    apply ZigzagExt.object_ext
    · intro j
      change Fin 3 at j
      fin_cases j <;> rfl
    · intro j
      change Fin 2 at j
      fin_cases j <;> rfl
  apply CategoryTheory.Functor.hext ho
  intro i j f
  apply ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change Fin 3 at k
  fin_cases k <;> rfl

/-- 同じ相対屋根の余極限への像は、元の正規化屋根の全制限である。 -/
lemma complexRelativeElementRoofMap_image :
    let := projectiveModelCategory A
    let QX := (framedLimitProbeFunctor A).obj X
    complexRelativeElementRoofMap A QX Y ≫
      (AsSmallComparison.colimitIso (weakEquivalences (Complex A)) QX Y).inv =
      (complexRelativeElementIndexIso A X Y).hom ≫ complexNormalizedTensorRoof A X Y := by
  let := projectiveModelCategory A
  let QX := (framedLimitProbeFunctor A).obj X
  let W := weakEquivalences (Complex A)
  have hg : graphInclusion (AsSmallComparison.weak W)
      ((complexRelativeUp A).obj QX) ((complexRelativeUp A).obj Y) LeftRoof.word ≫
      (AsSmallComparison.colimitIso W QX Y).inv =
    (AsSmallComparison.graphIso W QX Y LeftRoof.word).inv ≫
      graphInclusion W QX Y LeftRoof.word := by
    apply (cancel_epi (AsSmallComparison.graphIso W QX Y LeftRoof.word).hom).mp
    rw [← Category.assoc, ← AsSmallComparison.graphInclusion_colimitIso]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hgRel : graphInclusion (complexRelativeCategory A).weakEquivalences
      ((complexRelativeUp A).obj QX) ((complexRelativeUp A).obj Y) LeftRoof.word ≫
      (AsSmallComparison.colimitIso W QX Y).inv =
    (AsSmallComparison.graphIso W QX Y LeftRoof.word).inv ≫
      graphInclusion W QX Y LeftRoof.word := hg
  dsimp only [QX, W] at hgRel
  change (LeftRoof.Precompose.SameUniverse.diagramGraphMap
    (complexRelativeCategory A).weakEquivalences (complexRelativeElementRoof A QX Y) ≫
    graphInclusion _ _ _ LeftRoof.word) ≫ _ = _
  rw [Category.assoc, hgRel, ← Category.assoc, complexRelativeElementRoof_graph_image]
  simp only [complexNormalizedTensorRoof, FrameHom.frameLeftRoofColimitMap, Category.assoc]

end SerrePositivity.EInfinity.PowerOperation
