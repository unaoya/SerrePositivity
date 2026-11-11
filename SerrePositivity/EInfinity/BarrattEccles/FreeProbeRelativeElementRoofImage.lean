module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementRoof
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementNormalizedIndex
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedCommonRoofMaps
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofAugmentationImage
/-! 概要：元の相対自由 roof の全包含像を同じ正規化自由 roof へ同定する。
方針：元の全随伴評価・augmentation・縦射を全 zigzag 上で比較する。
規約：元の全要素圏と二本の実射を保持する。
使われ方：標準自由 Hom span から同じ相対 pinched 族の弱同値性を検出する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の相対自由 roof の全 graph 包含像は同じ随伴評価の全 roof。
方針：全列の対象・二射・全縦射を比較する。
規約：元の全単体を保持。使われ方：同じ reduced 屋根の包含像。 -/
lemma freeProbeRelativeElementRoof_graph_image :
    let := modelCategory A
    LeftRoof.Precompose.SameUniverse.diagramGraphMap
      (cofibrantAlgebraRelativeCategory A).weakEquivalences (freeProbeRelativeElementRoof A X B) ≫
      cofibrantAlgebraHammockGraphInclusionMap A (freeProbeRelativeElementSource A X)
        (ULiftHom.objUp.{u + 1, u + 1} B) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word =
    freeProbeRelativeElementNormalizedIndexNerveMap A X B ≫
      FrameHom.frameLeftRoofNerveMap (Y := B.obj) (weakEquivalences (operad A).Algebra)
        ((freeNormalizedProbeFrame A).obj X) ((freeNormalizedProbeAugmentation A).app X)
        (freeNormalizedProbeAugmentation_weak A X)
        (fun f => freeNormalizedProbeFrame_homotopicallyConstant A X f) := by
  let := modelCategory A
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let F := ((LeftRoof.Precompose.SameUniverse.diagramGraphMap
    (cofibrantAlgebraRelativeCategory A).weakEquivalences (freeProbeRelativeElementRoof A X B) ≫
    cofibrantAlgebraHammockGraphInclusionMap A (freeProbeRelativeElementSource A X)
      (ULiftHom.objUp.{u + 1, u + 1} B) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app n) σ
  let G := ((freeProbeRelativeElementNormalizedIndexNerveMap A X B ≫
    FrameHom.frameLeftRoofNerveMap (Y := B.obj) (weakEquivalences (operad A).Algebra)
      ((freeNormalizedProbeFrame A).obj X) ((freeNormalizedProbeAugmentation A).app X)
      (freeNormalizedProbeAugmentation_weak A X)
      (fun f => freeNormalizedProbeFrame_homotopicallyConstant A X f)).app n) σ
  have ho (i : Fin (n.unop.len + 1)) : F.obj i = G.obj i := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro j
      change Fin 3 at j
      fin_cases j <;> rfl
    · intro j
      change Fin 2 at j
      fin_cases j <;> rfl
  apply CategoryTheory.Functor.hext ho
  intro i j f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change Fin 3 at k
  fin_cases k <;> rfl

/-- 概要：同じ相対全屋根の reduced 代数包含像は元の正規化 roof の全制限。
方針：同じ graph 像と元の余極限包含・正規化を接続する。
規約：元の全パラメータを保持。使われ方：相対全屋根の弱同値性。 -/
lemma freeProbeRelativeElementRoofMap_image :
    freeProbeRelativeElementRoofMap A X B ≫
      cofibrantAlgebraHammockColimitInclusionMap A (freeProbeElementCofibrantSource A X) B =
    freeProbeRelativeElementNormalizedIndexNerveMap A X B ≫
      freeNormalizedTensorReducedRoof A X B.obj := by
  let := modelCategory A
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ≫
      cofibrantAlgebraHammockColimitInclusionMap A (freeProbeElementCofibrantSource A X) B =
      cofibrantAlgebraHammockGraphInclusionMap A (freeProbeRelativeElementSource A X)
        (ULiftHom.objUp.{u + 1, u + 1} B) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ≫
      algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ((freeProbeFunctor A).obj X) B.obj ≫
        (algebraHammockReductionIso A ((freeProbeFunctor A).obj X) B.obj).hom :=
    cofibrantAlgebraHammockColimitInclusionMap_graph A
      (freeProbeElementCofibrantSource A X) B _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
  change (LeftRoof.Precompose.SameUniverse.diagramGraphMap
    (cofibrantAlgebraRelativeCategory A).weakEquivalences (freeProbeRelativeElementRoof A X B) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word) ≫ _ = _
  rw [Category.assoc, hg,
    ← Category.assoc, ← Category.assoc, freeProbeRelativeElementRoof_graph_image]
  simp only [freeNormalizedTensorReducedRoof, FrameHom.frameLeftRoofColimitMap,
    algebraHammockGraphInclusion, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
