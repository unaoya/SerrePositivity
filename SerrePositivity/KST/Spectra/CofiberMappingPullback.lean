module

public import SerrePositivity.KST.Spectra.PointedCofiber
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：点つき cofiber からの写像空間を与える引き戻し。
方針：内部 Hom の源に関する反変関手が極限を保つことを使う。
規約：通常の単体集合の厳密な pullback の主張。
使われ方：Goerss–Jardine I §7、HTT A.3.3。loop と path fiber の比較。
-/

@[expose] public section

universe v w u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : PointedSimplicialSet.forget.{u}.IsRightAdjoint :=
  PointedObject.adjoinForgetAdjunction.isRightAdjoint

/-- 概要：標的を固定した点つき内部 Hom の基礎単体集合の反変関手。
方針：閉構造の反変 Hom と基点忘却を合成する。
規約：始域は点つき単体集合の反対圏。
使われ方：HTT A.3.3、Goerss–Jardine I §7。cofiber の Hom の pullback。 -/
def cofiberMappingFunctor (Z : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u}ᵒᵖ ⥤ SSet.{u} :=
  MonoidalClosed.internalHom.flip.obj Z ⋙ PointedSimplicialSet.forget

/-- 概要：反変写像空間関手は極限を保つ。
方針：閉構造のパラメータ付き随伴と忘却の右随伴性を合成する。
規約：任意の添字圏 J。
使われ方：HTT A.3.3。cofiber の pushout を Hom の pullback へ移す。 -/
instance cofiberMappingFunctor_preservesLimitsOfShape (Z : PointedSimplicialSet.{u})
    (J : Type v) [Category.{w} J] : PreservesLimitsOfShape J (cofiberMappingFunctor Z) := by
  dsimp only [cofiberMappingFunctor]
  infer_instance

/-- 概要：反変写像空間関手の射の作用は既存の源の制限。
方針：閉構造の pre と等化子による制限の一致を使う。
規約：任意の点つき射 i。
使われ方：Goerss–Jardine I §7。pullback の各辺の計算。 -/
@[simp]
theorem cofiberMappingFunctor_map (Z : PointedSimplicialSet.{u})
    {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y) :
    (cofiberMappingFunctor Z).map i.op = PointedMapping.pre i Z := by
  change ((MonoidalClosed.pre i).app Z).right = PointedMapping.pre i Z
  rw [← PointedMapping.prePointed_eq_closedPre]
  rfl

/-- 概要：cofiber からの点つき写像空間は構造制限の pullback。
方針：点つき pushout の反対に極限を保つ Hom 関手を適用する。
規約：Kan 性はこの圏論的な同定には不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path fiber の表示。 -/
theorem cofiberMapping_isPullback {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    IsPullback (PointedMapping.pre (pointedCofiberProjection i) Z)
      (PointedMapping.pre (PointedObject.fromPoint (pointedCofiber i)) Z)
      (PointedMapping.pre i Z) (PointedMapping.pre (PointedObject.toPoint X) Z) := by
  have h := ((pointedCofiber_isPushout i).op.flip).map (cofiberMappingFunctor Z)
  simpa only [cofiberMappingFunctor_map] using h

/-- 概要：点からの点つき Hom の基礎単体集合は終対象。
方針：点が初対象であることを極限保存の反変 Hom 関手で移す。
規約：点は smash の単位でなく零対象。
使われ方：Goerss–Jardine I §7。cofiber の Hom の pullback を基点 fiber に移す。 -/
def homPointIsTerminal (Z : PointedSimplicialSet.{u}) :
    IsTerminal (PointedObject.basedHom PointedObject.point Z).right :=
  IsTerminal.isTerminalObj (cofiberMappingFunctor Z) _ PointedObject.point_isZero.isInitial.op

end

end SerrePositivity.KST.Spectra
