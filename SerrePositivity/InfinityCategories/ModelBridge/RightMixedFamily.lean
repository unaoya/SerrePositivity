module

public import SerrePositivity.InfinityCategories.ModelBridge.RightFrameReplacement
public import SerrePositivity.InfinityCategories.ModelBridge.RightFrameInvariance

/-!
概要：同じ right frame と固定 source frame の混合比較を全標的で束ねる。
方針：元の augmentation の前後合成を自然変換にし、同じ次数零の後で反転する。
規約：元の全単体・全標的射を保ち、点ごとの逆を選ばない。
使われ方：right frame Hom と同じ hammock 全族との coherent な比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の両 frame の混合 Hom の全標的関手。
方針：同じ right frame の図式に固定 source frame の混合関手を合成する。
規約：全標的に厳密に自然。使われ方：同じ比較の共通標的。 -/
def rightMixedFamily : C ⥤ SSet.{v} := rightFrameDiagram r ⋙ MixedFrame.mixedFunctor q.obj

/-- 概要：元の source frame Hom から混合 Hom への全自然な比較。
方針：各全単体へ同じ right augmentation を後合成する。
規約：同じ実射。使われ方：fibrant な値の後の全族比較。 -/
def rightMixedLeft : cosimplicialHom q.obj ⟶ rightMixedFamily q r where
  app Y := MixedFrame.leftComparison q.obj ((rightFrameUnit r).app Y)
  naturality Y Z f := by
    ext n a
    change (a ≫ f) ≫ ((rightFrameUnit r).app Z).app n =
      (a ≫ ((rightFrameUnit r).app Y).app n) ≫ ((rightFrameDiagram r).map f).app n
    rw [Category.assoc]
    have h := congr_app ((rightFrameUnit r).naturality f) n
    change f ≫ ((rightFrameUnit r).app Z).app n =
      ((rightFrameUnit r).app Y).app n ≫ ((rightFrameDiagram r).map f).app n at h
    simpa only [Category.assoc] using congrArg (a ≫ ·) h

/-- 概要：元の right frame Hom から同じ混合 Hom への全自然な比較。
方針：同じ source augmentation を各全単体へ前合成する。
規約：全標的と全作用素を保持。使われ方：同じ自然比較の右脚。 -/
def rightMixedRight : rightFrameHom r X ⟶ rightMixedFamily q r where
  app Y := MixedFrame.rightComparison q.obj q.augmentation ((rightFrameDiagram r).obj Y)
  naturality Y Z f := by
    ext n a
    change q.augmentation.app n.unop ≫ (a ≫ ((rightFrameDiagram r).map f).app n) =
      (q.augmentation.app n.unop ≫ a) ≫ ((rightFrameDiagram r).map f).app n
    exact (Category.assoc _ _ _).symm

/-- 概要：元の right 比較の全成分は anodyne 反転後に同型。
方針：同じ Reedy cofibrancy と元の augmentation の弱同値性を使う。
規約：元の源だけ cofibrant。使われ方：全自然変換の反転。 -/
lemma rightMixedRight_isIso [IsCofibrant X] (Y : C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((rightMixedRight q r).app Y)) := by
  apply MixedFrame.rightComparison_isIso q.obj q.cofibrant q.augmentation
    q.augmentation_weakEquivalence
  change reedyLeft simplex (cofibrations Cᵒᵖ) (Limits.initial.to (r.obj.obj (op Y)))
  exact r.cofibrant (op Y)

/-- 概要：fibrant な標的では元の left 比較も反転後に同型。
方針：同じ right frame の全値の fibrancy と augmentation の弱同値性を使う。
規約：同じ元の射。使われ方：全標的への次数零置換後の比較。 -/
lemma rightMixedLeft_isIso (Y : C) [IsFibrant Y] :
    IsIso (AnodyneHomotopy.anodyneQ.map ((rightMixedLeft q r).app Y)) := by
  apply MixedFrame.leftComparison_isIso q.obj q.cofibrant ((rightFrameUnit r).app Y)
    (rightFrameDiagram_isFibrant r Y)
  intro n
  exact (rightFrameUnit_trivialCofibration r Y n).2

/-- 概要：同じ次数零で前合成した全 left 比較は反転後に自然同型。
方針：全値が fibrant な同じ置換の後で元の全自然変換を反転する。
規約：成分ごとの任意の逆は選ばない。使われ方：coherent 全標的比較。 -/
def rightMixedReplacedLeftIso :
    rightFrameReplacement r ⋙ cosimplicialHom q.obj ⋙ AnodyneHomotopy.anodyneQ ≅
      rightFrameReplacement r ⋙ rightMixedFamily q r ⋙ AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (rightFrameReplacement r)
    (rightMixedLeft q r)) AnodyneHomotopy.anodyneQ
  have : ∀ Y, IsIso (t.app Y) := fun Y => by
    have := rightFrameReplacement_isFibrant r Y
    exact rightMixedLeft_isIso q r _
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- 概要：同じ置換の後の right 比較を全自然同型として露出する。
方針：全成分の反転を一つの自然変換に適用する。
規約：元の全標的射。使われ方：全図式の自然性を保持した比較。 -/
def rightMixedReplacedRightIso [IsCofibrant X] :
    rightFrameReplacement r ⋙ rightFrameHom r X ⋙ AnodyneHomotopy.anodyneQ ≅
      rightFrameReplacement r ⋙ rightMixedFamily q r ⋙ AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (Functor.whiskerLeft (rightFrameReplacement r)
    (rightMixedRight q r)) AnodyneHomotopy.anodyneQ
  have : ∀ Y, IsIso (t.app Y) := fun Y => rightMixedRight_isIso q r _
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- 概要：元の right frame Hom と置換後の Hom は全標的で自然同型。
方針：同じ元の置換単位の像の反転性を全自然変換に適用する。
規約：指定 right frame の次数零以外の置換は使わない。
使われ方：元の全標的へ比較を戻す。 -/
def rightFrameReplacementHomIso [IsCofibrant X] :
    rightFrameHom r X ⋙ AnodyneHomotopy.anodyneQ ≅
      rightFrameReplacement r ⋙ rightFrameHom r X ⋙ AnodyneHomotopy.anodyneQ := by
  let t := Functor.whiskerRight (rightFrameReplacementUnit r) (rightFrameHom r X)
  have : ∀ Y, IsIso ((Functor.whiskerRight t AnodyneHomotopy.anodyneQ).app Y) := fun Y =>
    rightFrameHom_map_isIso r X ((rightFrameReplacementUnit r).app Y)
      (rightFrameReplacementUnit_trivialCofibration r Y).2 AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)
  have : IsIso (Functor.whiskerRight t AnodyneHomotopy.anodyneQ) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight t AnodyneHomotopy.anodyneQ)

/-- 概要：元の right Hom を同じ置換後の source Hom へ全標的で比較する。
方針：同じ三つの自然同型を順に合成する。
規約：全図式の自然性を保持。使われ方：実 hammock 比較への接続。 -/
def rightFrameToSourceFamilyIso [IsCofibrant X] :
    rightFrameHom r X ⋙ AnodyneHomotopy.anodyneQ ≅
      rightFrameReplacement r ⋙ cosimplicialHom q.obj ⋙ AnodyneHomotopy.anodyneQ :=
  (rightFrameReplacementHomIso r).trans
    ((rightMixedReplacedRightIso q r).trans (rightMixedReplacedLeftIso q r).symm)

end SerrePositivity.EInfinity.FrameHom
