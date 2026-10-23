module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePathInternalHom

/-!
概要：引き戻し候補と関手単体集合の間の比較射と逆向きの射。
方針：可逆 path と内部 Hom の交換により、二射影と path を保って移す。
規約：試験 K は任意の単体集合。比較を定義するために必要なのは標的 C の quasicategory 性。
使われ方：Cat_∞ の引き戻しの全試験関手空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}}

/-- 概要：可逆 path と内部 Hom の交換の逆射も両端点を保つ。
方針：順方向の端点の公式へ逆射を合成する。
規約：i=0 が始点、i=1 が終点。
使われ方：関手空間側の指定 path の端点の確認。 -/
lemma catPullbackPathInternalHom_inv_endpoint (K C : SSet.{u}) [Quasicategory C] (i : Fin 2) :
    (equivalencePathInternalHomIso K C).inv ≫ equivalencePathEndpoint ((ihom K).obj C) i =
      (ihom K).map (equivalencePathEndpoint C i) := by
  rw [← equivalencePathInternalHomIso_endpoint K C i, Iso.inv_hom_id_assoc]

/-- 概要：候補への K パラメータの関手を関手空間側の候補へ送る。
方針：二射影を後合成し、path 成分を内部 Hom の交換で移す。
規約：可逆 path の始点・終点と元の二関手を厳密に保つ。
使われ方：全試験対象の関手空間の比較の順方向。 -/
def catPullbackFunctorMap (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    (ihom K).obj (catPullback p q) ⟶ catPullback ((ihom K).map p) ((ihom K).map q) :=
  catPullbackLift _ _ ((ihom K).map (catPullbackFst p q)) ((ihom K).map (catPullbackSnd p q))
    ((ihom K).map (catPullbackPath p q) ≫ (equivalencePathInternalHomIso K C).inv)
    (by rw [Category.assoc, catPullbackPathInternalHom_inv_endpoint, ← Functor.map_comp,
      catPullbackPath_zero, Functor.map_comp])
    (by rw [Category.assoc, catPullbackPathInternalHom_inv_endpoint, ← Functor.map_comp,
      catPullbackPath_one, Functor.map_comp])

/-- 概要：関手空間側の候補を候補への K パラメータの関手へ送る。
方針：path を交換の順射で戻し、三成分を uncurry して lift した後に curry する。
規約：全単体の族として定義し、頂点ごとの選択を用いない。
使われ方：全試験対象の関手空間の比較の逆方向。 -/
def catPullbackFunctorInv (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    catPullback ((ihom K).map p) ((ihom K).map q) ⟶ (ihom K).obj (catPullback p q) :=
  curry (catPullbackLift p q
    (uncurry (catPullbackFst ((ihom K).map p) ((ihom K).map q)))
    (uncurry (catPullbackSnd ((ihom K).map p) ((ihom K).map q)))
    (uncurry (catPullbackPath ((ihom K).map p) ((ihom K).map q) ≫
      (equivalencePathInternalHomIso K C).hom))
    (by rw [← uncurry_natural_right, Category.assoc,
      equivalencePathInternalHomIso_endpoint, catPullbackPath_zero, uncurry_natural_right])
    (by rw [← uncurry_natural_right, Category.assoc,
      equivalencePathInternalHomIso_endpoint, catPullbackPath_one, uncurry_natural_right]))

end SerrePositivity.InfinityCategories.F2
