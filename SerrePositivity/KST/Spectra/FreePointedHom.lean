module

public import SerrePositivity.Spectra.Pointed.AdjoinBasepointProduct
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：自由に基点を加えた源からの点つき内部 Hom と通常の内部 Hom の自然同型。
方針：自由基点の smash と直積の比較で左随伴を同定し、右随伴の一意性を使う。
規約：既存 Spectra から借りるのは余積・smash の通常の圏論的な基礎だけ。
使われ方：HA §1.4.2、BF 1978 §2。点つき重み付き end と Kan の end の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.FreePointedHom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自由基点を加えた対象との smash は、先に直積を取り基点を加える操作と自然同型。
方針：既存の自由基点の smash と直積の同型を片変数で束ねる。
規約：左因子 A を固定する。
使われ方：HA §1.4.2。内部 Hom の二つの右随伴の左辺の比較。 -/
def tensorNatIso (A : SSet.{u}) :
    PointedObject.adjoinFunctor ⋙ tensorLeft (PointedObject.adjoin A) ≅
      tensorLeft A ⋙ PointedObject.adjoinFunctor :=
  NatIso.ofComponents (fun B ↦ PointedObject.adjoinSmashIso A B) (fun {X Y} f ↦ by
    change PointedObject.smashMap (𝟙 (PointedObject.adjoin A))
      (PointedObject.adjoinFunctor.map f) ≫ PointedObject.adjoinSmashHom A Y =
      PointedObject.adjoinSmashHom A X ≫ PointedObject.adjoinFunctor.map (A ◁ f)
    have h := PointedObject.adjoinSmashHom_naturality (C := SSet.{u}) (𝟙 A) f
    rw [CategoryTheory.Functor.map_id, id_tensorHom] at h
    exact h)

/-- 概要：自由基点を加えた源からの点つき内部 Hom の忘却は通常の内部 Hom と自然同型。
方針：自由基点と閉構造の二つの随伴を合成し、左辺の自然同型から右随伴を同定する。
規約：標的の Kan 性を仮定しない通常の自然同型。
使われ方：HA §1.4.2、BF 1978 §2。pointed end の underlying Kan end との接続。 -/
def natIso (A : SSet.{u}) :
    ihom (PointedObject.adjoin A) ⋙ PointedSimplicialSet.forget ≅
      PointedSimplicialSet.forget ⋙ ihom A :=
  (PointedObject.adjoinForgetAdjunction.comp (ihom.adjunction (PointedObject.adjoin A))).rightAdjointUniq
    (((ihom.adjunction A).comp PointedObject.adjoinForgetAdjunction).ofNatIsoLeft
      (tensorNatIso A).symm)

/-- 概要：自由基点を加えた源からの内部 Hom の比較を指定した標的で評価する。
方針：右随伴の自然同型の成分を取る。
規約：点つき標的 Y は任意。
使われ方：HA §1.4.2。点つき end の成分ごとの比較。 -/
def iso (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (PointedObject.adjoin A) Y).right ≅ (ihom A).obj Y.right :=
  (natIso A).app Y

end

end SerrePositivity.KST.Spectra.FreePointedHom
