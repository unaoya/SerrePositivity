module

public import SerrePositivity.KST.Spectra.PointedFreeActionEquivalence

/-!
概要：点つき作用の係数図式の関手と後合成の自然な交換。
方針：作用を一対象圏上の図式へ送る操作を通常の関手の段階で比較する。
規約：end の構成に先立つ図式の自然同型だけを使う。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の loop 交換の係数比較。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき作用の係数図式を作用の圏からの関手にする。
方針：作用の図式表示と小さな圏への前合成を合成する。
規約：各対象は既存の pointedCoefficients と同じ図式。
使われ方：Goerss–Jardine VIII §2。係数の図式の関手的な比較。 -/
def pointedCoefficientsFunctor (G : Type u) [Group G] :
    Action PointedSimplicialSet.{u} G ⥤
      (AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}) :=
  Action.FunctorCategoryEquivalence.functor ⋙
    (Functor.whiskeringLeft (AsSmall.{u} (SingleObj G)) (SingleObj G)
      PointedSimplicialSet.{u}).obj AsSmall.down

/-- 概要：作用の係数図式を取る操作は任意の後合成関手と自然に交換する。
方針：両側の対象と射は同じ成分なので恒等の成分を与える。
規約：通常の図式の同型であり、Kan 性を使わない。
使われ方：Goerss–Jardine VIII §2。内部 Hom を作用の係数の外へ移す比較。 -/
def pointedCoefficientsPostIso (G : Type u) [Group G]
    (F : PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u}) :
    pointedCoefficientsFunctor G ⋙
        (Functor.whiskeringRight (AsSmall.{u} (SingleObj G)) PointedSimplicialSet.{u}
          PointedSimplicialSet.{u}).obj F ≅
      F.mapAction G ⋙ pointedCoefficientsFunctor G :=
  NatIso.ofComponents (fun B ↦ Iso.refl _) (fun _ ↦ by rfl)

end

end SerrePositivity.KST.Spectra.FreeActionFamily
