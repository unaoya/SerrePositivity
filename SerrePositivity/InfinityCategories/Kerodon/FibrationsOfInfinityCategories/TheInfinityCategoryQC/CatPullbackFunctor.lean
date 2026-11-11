module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom

/-!
概要：引き戻し候補と関手単体集合の間の比較射と逆向きの射。
方針：可逆 path と内部 Hom の交換により、二射影と path を保って移す。
規約：試験 K は任意の単体集合。比較を定義するために必要なのは標的 C の quasicategory 性。
使われ方：Cat_∞ の引き戻しの全試験関手空間の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：可逆 path と内部 Hom の交換の逆射も両端点を保つ。
方針：順方向の端点の公式へ逆射を合成する。
規約：i=0 が始点、i=1 が終点。
使われ方：関手空間側の指定 path の端点の確認。 -/
lemma catPullbackPathInternalHom_inv_endpoint (K C : SSet.{u}) [Quasicategory C] (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso K C).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom K).obj C) i =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C i) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_endpoint K C i, Iso.inv_hom_id_assoc]

/-- 概要：候補への K パラメータの関手を関手空間側の候補へ送る。
方針：二射影を後合成し、path 成分を内部 Hom の交換で移す。
規約：可逆 path の始点・終点と元の二関手を厳密に保つ。
使われ方：全試験対象の関手空間の比較の順方向。 -/
def catPullbackFunctorMap (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback ((ihom K).map p) ((ihom K).map q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift _ _ ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q)) ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q))
    ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso K C).inv)
    (by rw [Category.assoc, catPullbackPathInternalHom_inv_endpoint, ← Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_zero, Functor.map_comp])
    (by rw [Category.assoc, catPullbackPathInternalHom_inv_endpoint, ← Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_one, Functor.map_comp])

/-- 概要：関手空間側の候補を候補への K パラメータの関手へ送る。
方針：path を交換の順射で戻し、三成分を uncurry して lift した後に curry する。
規約：全単体の族として定義し、頂点ごとの選択を用いない。
使われ方：全試験対象の関手空間の比較の逆方向。 -/
def catPullbackFunctorInv (K : SSet.{u}) (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback ((ihom K).map p) ((ihom K).map q) ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackLift p q
    (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst ((ihom K).map p) ((ihom K).map q)))
    (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd ((ihom K).map p) ((ihom K).map q)))
    (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath ((ihom K).map p) ((ihom K).map q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso K C).hom))
    (by rw [← uncurry_natural_right, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_endpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_zero, uncurry_natural_right])
    (by rw [← uncurry_natural_right, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalencePathInternalHomIso_endpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_one, uncurry_natural_right]))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
