module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFramePostcompose
public import SerrePositivity.EInfinity.FrameHom.FrameLeftRoofPrecompose

/-!
# 元の source frame 比較の始域自然性

概要：元の始域射を持つ関手的分解の比較を同じ reduced 比較へ移す。
方針：元の四列ホモトピーと augmentation の全自然性を使う。
規約：元の分解・始域射・比較を保持する。
使われ方：既存 Map^h の比較の始域自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite Hammock SerrePositivity.SimplicialModel
open SerrePositivity.Reedy
variable (A : Type u) [CommRing A] (Y : (operad A).Algebra) {X' X : (operad A).Algebra}

def sourceFramePrecomposeIndexMap (f : X' ⟶ X) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X')).obj Y).Elements)ᵒᵖ)) :=
  nerveMap (ULiftHom.down.{0, u, u + 1} ⋙
    (((sourceFrameHom A).map f.op).app Y).mapElements.op ⋙ ULiftHom.up)

def algebraReducedHammockPrecompose (f : X' ⟶ X) :
    algebraReducedHammock A X Y ⟶ algebraReducedHammock A X' Y := by
  let := modelCategory A
  exact reducedPrecomposeMap (weakEquivalences (operad A).Algebra) Y f

lemma sourceFrameReducedHammockNerveMap_precompose (f : X' ⟶ X) :
    AnodyneHomotopy.anodyneQ.map
        (sourceFramePrecomposeIndexMap A Y f ≫ sourceFrameReducedHammockNerveMap A X' Y) =
      AnodyneHomotopy.anodyneQ.map (sourceFrameReducedHammockNerveMap A X Y) ≫
        AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPrecompose A Y f) := by
  let := modelCategory A
  let Q := AnodyneHomotopy.anodyneQ
  let F := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let q' := F.atObject X'
  let q := F.atObject X
  have h := FrameHom.frameLeftRoofColimitMap_precompose (Y := Y)
    (weakEquivalences (operad A).Algebra) q'.obj q.obj
    q'.augmentation q'.augmentation_weakEquivalence q.augmentation q.augmentation_weakEquivalence
    (fun a => q'.homotopicallyConstant a) (fun a => q.homotopicallyConstant a)
    (F.obj.map f) f (F.augmentation.naturality f)
  change Q.map (sourceFramePrecomposeIndexMap A Y f ≫
      (sourceFrameLeftRoofNerveMap A X' Y ≫ algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X' Y)) =
    Q.map (sourceFrameLeftRoofNerveMap A X Y ≫ algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y) ≫
      Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences (operad A).Algebra) f) Y) at h
  have hn : (algebraHammockReductionIso A X Y).hom ≫ algebraReducedHammockPrecompose A Y f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences (operad A).Algebra) f) Y ≫
        (algebraHammockReductionIso A X' Y).hom :=
    reducedColimitIso_precompose (weakEquivalences (operad A).Algebra) Y f
  have hnQ := congrArg Q.map hn
  simp only [Functor.map_comp] at hnQ
  rw [← sourceFrameLeftRoofNerveMap_normalization, ← sourceFrameLeftRoofNerveMap_normalization]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnQ]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k => k ≫ Q.map (algebraHammockReductionIso A X' Y).hom) h

lemma sourceFramePrecomposeIndexMap_augmentation (f : X' ⟶ X) :
    sourceFramePrecomposeIndexMap A Y f ≫ sourceFrameIndexAugmentation A X' Y =
      sourceFrameIndexAugmentation A X Y ≫ SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHom A).map f.op).app Y) :=
  FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality _

lemma sourceFrameReducedHammockComparison_precompose (f : X' ⟶ X) :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHom A).map f.op).app Y)) ≫
      sourceFrameReducedHammockComparison A X' Y =
    sourceFrameReducedHammockComparison A X Y ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPrecompose A Y f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  have h := congrArg Q.map (sourceFramePrecomposeIndexMap_augmentation A Y f)
  simp only [Functor.map_comp] at h
  apply (cancel_epi (Q.map (sourceFrameIndexAugmentation A X Y))).mp
  rw [← Category.assoc, ← h, Category.assoc, sourceFrameReducedHammockComparison_fac,
    ← Q.map_comp, sourceFrameReducedHammockNerveMap_precompose,
    ← sourceFrameReducedHammockComparison_fac, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
