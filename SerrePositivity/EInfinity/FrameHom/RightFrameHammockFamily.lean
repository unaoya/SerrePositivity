module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.RightMixedFamily
public import SerrePositivity.EInfinity.FrameHom.SourceRoofFamily
public import SerrePositivity.EInfinity.Hammock.WeakArrowActionEquivalences
public import SerrePositivity.EInfinity.Hammock.WeakAnodyneLocalization

/-!
概要：実 right frame Hom と元の hammock Hom を全標的の自然同型で比較する。
方針：同じ混合 Hom・全要素 nerve・次数零置換を三つの全自然変換で接続する。
規約：anodyne 局所化での全族比較であり、指定 ∞ 局所化への完成定理と区別する。
使われ方：全 coherent 比較の構成と同じ実射の弱同値性の検出。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uD vD
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Hammock
open SerrePositivity.Reedy
open SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
/-- 概要：元の right frame の置換単位を全標的の反転後の自然同型にする。
方針：同じ弱な単位の像を一つの自然変換として反転する。
規約：元の全標的射。使われ方：全図式への前合成。 -/
def rightFrameReplacementHomImageIso [IsCofibrant X] :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L ≅ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L := by
  let t := Functor.whiskerRight
    (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X)) L
  have : ∀ Y, IsIso (t.app Y) := fun Y => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_map_isIso r X
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Y).2 L hL
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

include hL in
/-- 概要：同じ混合 Hom の右比較を任意の anodyne 反転関手で一斉に反転する。
方針：元の比較の全成分の反転性を自然変換に適用する。
規約：元の全単体と全標的。使われ方：宇宙を揃えた全族比較。 -/
def rightMixedReplacedRightImageIso [IsCofibrant X] :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L ≅
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedFamily q r ⋙ L := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight q r)) L
  have : ∀ Y, IsIso (t.app Y) := fun Y =>
    AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight_isIso q r _)
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

include hL in
/-- 概要：同じ混合 Hom の左比較も全標的で同時に反転する。
方針：同じ置換後の fibrancy と全成分の反転性を使う。
規約：同じ次数零の後でのみ fibrancy を使う。
使われ方：全 source Hom 族の回収。 -/
def rightMixedReplacedLeftImageIso :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙ L ≅
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedFamily q r ⋙ L := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft q r)) L
  have : ∀ Y, IsIso (t.app Y) := fun Y => by
    have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r Y
    exact AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft_isIso q r _)
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

include hL in
/-- 概要：元の right Hom と同じ source Hom は全標的で反転後に自然同型。
方針：元の単位と混合比較の同じ三つの自然同型を合成する。
規約：同じ全比較を保つ。使われ方：大きい宇宙での実 hammock 比較。 -/
def rightFrameToSourceImageIso [IsCofibrant X] :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L ≅ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙ L :=
  (rightFrameReplacementHomImageIso r L hL).trans
    ((rightMixedReplacedRightImageIso q r L hL).trans
      (rightMixedReplacedLeftImageIso q r L hL).symm)

variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

/-- 概要：元の全要素 augmentation を同じ置換後に全自然同型として回収する。
方針：元の終端 augmentation の全成分を一つの自然変換として反転する。
規約：同じ元の全単体。使われ方：実 roof 族の左比較。 -/
def sourceFrameReplacedAugmentationIso :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ sourceFrameElementsFamily q ⋙ AnodyneHomotopy.anodyneQ ≅
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙
        SSet.uliftFunctor.{max u v, v} ⋙ AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r)
    (sourceFrameElementsAugmentation q)) AnodyneHomotopy.anodyneQ
  have : ∀ Y, IsIso (t.app Y) := fun Y =>
    SimplexTerminalNerve.liftedAugmentation_localized_isIso _
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

include cof in
/-- 概要：元の二列 roof の全標的比較は同じ置換後に反転後の自然同型。
方針：全 source roof の弱比較を元の自然変換に適用する。
規約：第一分解と指定 right frame。使われ方：全族の hammock 回収。 -/
def sourceRoofReplacedIso :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ sourceFrameElementsFamily q ⋙ AnodyneHomotopy.anodyneQ ≅
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ hammockHomFamily (weakEquivalences C) X ⋙
        AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r)
    (sourceRoofFamily q)) AnodyneHomotopy.anodyneQ
  have : ∀ Y, IsIso (t.app Y) := fun Y => by
    have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r Y
    exact Hammock.anodyneQ_map_isIso_of_weak _
      (resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first q _ r cof)
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

/-- 概要：同じ次数零置換は元の hammock Hom の全族を反転後に保つ。
方針：元の単位の弱同値による後合成を一つの自然変換で反転する。
規約：同じ元の hammock 合成。使われ方：全標的への復帰。 -/
def hammockReplacementFamilyIso :
    hammockHomFamily (weakEquivalences C) X ⋙ AnodyneHomotopy.anodyneQ ≅
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ hammockHomFamily (weakEquivalences C) X ⋙
        AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r)
    (hammockHomFamily (weakEquivalences C) X)) AnodyneHomotopy.anodyneQ
  have : ∀ Y, IsIso (t.app Y) := fun Y =>
    (WeakArrow.postcompositionIso ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Y).2 X AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

/-- 概要：元の right frame Hom と元の hammock Hom を全標的で同時に比較する。
方針：同じ混合比較・全要素 augmentation・roof と置換単位の自然同型を合成する。
規約：全図式の自然性を保持し、指定 ∞ 局所化の比較は別に接続する。
使われ方：その coherent 比較の同じ全族の検出。 -/
def rightFrameHammockFamilyIso [IsCofibrant X] :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ SSet.uliftFunctor.{max u v, v} ⋙ AnodyneHomotopy.anodyneQ ≅
      hammockHomFamily (weakEquivalences C) X ⋙ AnodyneHomotopy.anodyneQ :=
  (rightFrameToSourceImageIso q r
    (SSet.uliftFunctor.{max u v, v} ⋙ AnodyneHomotopy.anodyneQ)
    UniverseLift.anodyneQ_lift_inverts).trans
      ((sourceFrameReplacedAugmentationIso q r).symm.trans
        ((sourceRoofReplacedIso q r cof).trans (hammockReplacementFamilyIso r).symm))

end SerrePositivity.EInfinity.FrameHom
