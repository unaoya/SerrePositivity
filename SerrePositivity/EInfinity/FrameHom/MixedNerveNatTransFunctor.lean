module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveNatTrans
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTrans
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
/-! 概要：混合宇宙の元の通常自然変換を全関手圏の射へ関手的に送る。
方針：同じ Hom 持ち上げと nerve 比較を前後合成し、元の全図式へ戻す。
規約：元の円柱・全図式を保持し、点ごとの比較を使わない。
使われ方：自由随伴単位の全自然変換正方形の導来像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C D : Type (u + 1)) [Category.{u} C] [Category.{u} D]

/-- 概要：元の通常関手と全自然変換を同じ Hom 宇宙へ持ち上げる。
方針：既存の lifted と liftedNatTrans を束ねる。
規約：同じ対象・射を保持。使われ方：全自然変換の関手性。 -/
def liftedFunctor : (C ⥤ D) ⥤ (ULiftHom.{u + 1} C ⥤ ULiftHom.{u + 1} D) where
  obj := lifted
  map η := liftedNatTrans η

/-- 概要：持ち上げた通常自然変換の全 h Fun 比較。
方針：同じ nerve 比較と元の up・down による全前後合成を使う。
規約：全パラメータを保持。使われ方：元の円柱との比較。 -/
def rawHomFunctor : (C ⥤ D) ⥤ hoFunctor.obj ((ihom (nerve C)).obj (nerve D)) :=
  liftedFunctor C D ⋙
    F1B.nerveFunctorHomEmbedding (ULiftHom.{u + 1} C) (ULiftHom.{u + 1} D) ⋙
    (hoFunctor.map ((pre (up C)).app (nerve (ULiftHom.{u + 1} D)))).toFunctor ⋙
    (hoFunctor.map ((ihom (nerve C)).map (down D))).toFunctor

/-- 概要：回収等式で元の nerve 関手そのものを対象とする全比較関手。
方針：同じ raw 関手を厳密な recover の等式に沿って移す。
規約：元の全射を変更しない。使われ方：自然変換の合成保存。 -/
def homFunctor : (C ⥤ D) ⥤ hoFunctor.obj ((ihom (nerve C)).obj (nerve D)) :=
  (rawHomFunctor C D).copyObj (fun F => HomotopyCategory.mk (functorVertex (nerveMap F)))
    (fun F => eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) (recover F)))

/-- 概要：元の混合宇宙円柱自身は同じ比較関手の射。
方針：全前後合成の円柱公式と recover の両端輸送を照合する。
規約：元の円柱を保持。使われ方：全自然変換の合成則。 -/
lemma homFunctor_map {F G : C ⥤ D} (η : F ⟶ G) :
    (homFunctor C D).map η =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (homotopy η)) := by
  change (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (recover F))).inv ≫
    (hoFunctor.map ((ihom (nerve C)).map (down D))).toFunctor.map
      ((hoFunctor.map ((pre (up C)).app (nerve (ULiftHom.{u + 1} D)))).toFunctor.map
        (F1B.nerveNatTransHom (liftedNatTrans η))) ≫
      (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
        (recover G))).hom = _
  have hb : F1B.nerveNatTransHom (liftedNatTrans η) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (F1B.nerveNatTransHomotopy (liftedNatTrans η))) :=
    (F1B.nerveNatTransHomotopy_hom (liftedNatTrans η)).symm
  rw [hb, ← functorHomotopyPrecomp_hom, ← functorHomotopyPostcomp_hom]
  exact homMk_transport (congrArg functorVertex (recover F))
    (congrArg functorVertex (recover G)) _ _ rfl

/-- 概要：元の二つの混合宇宙円柱の合成は同じ自然変換の合成。
方針：元の全比較関手の合成保存を使う。
規約：全関手圏で比較。使われ方：元の単位正方形の導来像。 -/
lemma homotopy_hom_comp {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (homotopy (η ≫ θ))) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (homotopy η)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (homotopy θ)) := by
  rw [← homFunctor_map, ← homFunctor_map, ← homFunctor_map]
  exact (homFunctor C D).map_comp η θ

end SerrePositivity.EInfinity.FrameHom.MixedNerve
