module
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedCommonRoofMaps
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization
/-! 概要：元の標準自由 Hom span と同じ正規化二列 roof の全比較。
方針：元の左右 frame 射を四列比較へ代入し、全要素圏の反転性で検出する。
規約：元の全比較射とパラメータを保持する。
使われ方：元の全 pinched 族の弱同値性と標準単位比較の検出。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite HomotopicalAlgebra Hammock
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：元の標準自由 Hom から共通 Hom への全要素圏写像は反転される。
方針：同じ実 Hom 弱比較を全要素圏の反転性へ渡す。
規約：元の射を保持。使われ方：共通屋根の弱同値性。 -/
lemma freeNormalizedCommonLeftIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonLeftIndex A X B))) := by
  let := modelCategory A
  have : SSet.KanComplex ((((freeProbeFunctor A).op ⋙ sourceFrameHom A).obj (op X)).obj B) :=
    sourceFrameHom_kanComplex A (op ((freeProbeFunctor A).obj X)) B
  have := freeNormalizedHomMiddle_kanComplex A (op X) B
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (freeNormalizedHomFromStandard_homotopyEquivalence A (op X) B)
  exact FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

/-- 概要：元の正規化 Hom から共通 Hom への全要素圏写像は反転される。
方針：同じ実 Hom 弱比較を全要素圏の反転性へ渡す。
規約：元の射を保持。使われ方：正規化屋根の弱同値性。 -/
lemma freeNormalizedCommonRightIndex_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonRightIndex A X B))) := by
  have := freeNormalizedProbeHom_kanComplex A (op X) B
  have := freeNormalizedHomMiddle_kanComplex A (op X) B
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (freeNormalizedHomFromTensor_homotopyEquivalence A (op X) B)
  exact FrameHom.frameSpanSourceIndexMap_localized_isIso _ _ _
    (anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence)

/-- 概要：元の標準自由 Hom 側の全二列 roof 比較。
方針：元の左射と全 augmentation 三角形を同じ四列比較へ渡す。
規約：全単体と元の標準 roof 自身を保持。使われ方：共通屋根の反転性。 -/
lemma freeNormalizedCommonReducedRoof_left_comparison :
    AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonLeftIndex A X B)) ≫
      AnodyneHomotopy.anodyneQ.map (freeNormalizedCommonReducedRoof A X B) =
    AnodyneHomotopy.anodyneQ.map
      (sourceFrameReducedHammockNerveMap A ((freeProbeFunctor A).obj X) B) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject
    ((freeProbeFunctor A).obj X)
  let W := weakEquivalences (operad A).Algebra
  let rC := FrameHom.frameLeftRoofColimitMap (Y := B) W
    ((freeNormalizedCommonFrame A).obj X) ((freeNormalizedCommonFrameAugmentation A).app X)
    (freeNormalizedCommonFrameAugmentation_weak A X)
    (fun f => freeNormalizedCommonFrame_map_weak A X f)
  let rS := FrameHom.frameLeftRoofColimitMap (Y := B) W q.obj q.augmentation
    q.augmentation_weakEquivalence (fun f => q.homotopicallyConstant f)
  let red := (algebraHammockReductionIso A ((freeProbeFunctor A).obj X) B).hom
  have hc : AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonLeftIndex A X B)) ≫
      AnodyneHomotopy.anodyneQ.map rC = AnodyneHomotopy.anodyneQ.map rS :=
    FrameHom.frameLeftRoofColimitMap_comparison _ _ _ W _ _ _ _ _ _
      (congr_app (freeNormalizedCommonFrameLeft_over A) X)
  have hs : rS ≫ red = sourceFrameReducedHammockNerveMap A ((freeProbeFunctor A).obj X) B :=
    sourceFrameLeftRoofNerveMap_normalization A ((freeProbeFunctor A).obj X) B
  change AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonLeftIndex A X B)) ≫
    AnodyneHomotopy.anodyneQ.map (rC ≫ red) = _
  rw [Functor.map_comp, ← Category.assoc, hc, ← Functor.map_comp, hs]

/-- 概要：元の正規化自由 Hom 側の全二列 roof 比較。
方針：元の右射と同じ augmentation を四列比較へ渡す。
規約：全単体と元の正規化 roof 自身を保持。使われ方：正規化屋根の反転性。 -/
lemma freeNormalizedCommonReducedRoof_right_comparison :
    AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonRightIndex A X B)) ≫
      AnodyneHomotopy.anodyneQ.map (freeNormalizedCommonReducedRoof A X B) =
    AnodyneHomotopy.anodyneQ.map (freeNormalizedTensorReducedRoof A X B) := by
  let := modelCategory A
  let W := weakEquivalences (operad A).Algebra
  let rC := FrameHom.frameLeftRoofColimitMap (Y := B) W
    ((freeNormalizedCommonFrame A).obj X) ((freeNormalizedCommonFrameAugmentation A).app X)
    (freeNormalizedCommonFrameAugmentation_weak A X)
    (fun f => freeNormalizedCommonFrame_map_weak A X f)
  let rT := FrameHom.frameLeftRoofColimitMap (Y := B) W
    ((freeNormalizedProbeFrame A).obj X) ((freeNormalizedProbeAugmentation A).app X)
    (freeNormalizedProbeAugmentation_weak A X)
    (fun f => freeNormalizedProbeFrame_homotopicallyConstant A X f)
  let red := (algebraHammockReductionIso A ((freeProbeFunctor A).obj X) B).hom
  have hc : AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonRightIndex A X B)) ≫
      AnodyneHomotopy.anodyneQ.map rC = AnodyneHomotopy.anodyneQ.map rT :=
    FrameHom.frameLeftRoofColimitMap_comparison _ _ _ W _ _ _ _ _ _ rfl
  change AnodyneHomotopy.anodyneQ.map (nerveMap (freeNormalizedCommonRightIndex A X B)) ≫
    AnodyneHomotopy.anodyneQ.map (rC ≫ red) = AnodyneHomotopy.anodyneQ.map (rT ≫ red)
  rw [Functor.map_comp, ← Category.assoc, hc, ← Functor.map_comp]

/-- 概要：元の共通 frame の全 reduced roof は弱同値。
方針：元の標準 roof と左の実 Hom span の反転性から反映する。
規約：元の全屋根自身を検証。使われ方：正規化自由屋根の弱同値性。 -/
lemma freeNormalizedCommonReducedRoof_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeNormalizedCommonReducedRoof A X B) := by
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := freeNormalizedCommonLeftIndex_localized_isIso A X B
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (freeNormalizedCommonLeftIndex A X B)) ≫
      AnodyneHomotopy.anodyneQ.map (freeNormalizedCommonReducedRoof A X B)) := by
    rw [freeNormalizedCommonReducedRoof_left_comparison]
    exact anodyneQ_map_isIso_of_weak _
      (sourceFrameReducedHammockNerveMap_weak A ((freeProbeFunctor A).obj X) B)
  exact (isIso_comp_left_iff _ _).mp hc

/-- 概要：元の正規化自由 frame の全 reduced roof は弱同値。
方針：同じ共通 roof と右の実 Hom span の全比較を使う。
規約：元の全屋根自身を検証。使われ方：標準単位誘導射の弱同値判定。 -/
lemma freeNormalizedTensorReducedRoof_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeNormalizedTensorReducedRoof A X B) := by
  apply FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := freeNormalizedCommonRightIndex_localized_isIso A X B
  have := anodyneQ_map_isIso_of_weak _ (freeNormalizedCommonReducedRoof_weak A X B)
  rw [← freeNormalizedCommonReducedRoof_right_comparison]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
