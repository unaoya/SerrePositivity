module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryFirstPrecomposition

/-!
概要：指定関手間射の前合成と後合成を、同じ内部 Hom の自然性で交換する。
方針：正規化した射作用の合成則へ戻して pre の自然性を使う。
規約：元の射を保持する。使われ方：E01 の指定比較の単位回収式の点評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：指定射の前合成と後合成は結合順序の表示を除いて一致する。
方針：内部前合成の自然性を同じホモトピー圏の射作用に適用する。
規約：全パラメータと元の指定射を保持する。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3の
Yoneda 比較の指定単位との両立式を点評価する計算法則。 -/
lemma postcompose_precomposeFunctorHom_heq {A B X Y : SSet.{u}}
    (k : B ⟶ A) (q : X ⟶ Y) {F G : A ⟶ X} (α : FunctorHom F G) :
    HEq (postcomposeFunctorHom q (precomposeFunctorHom k α))
      (precomposeFunctorHom k (postcomposeFunctorHom q α)) := by
  unfold precomposeFunctorHom postcomposeFunctorHom
  rw [normalizedVertexHomMap_comp, normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map ((pre k).app X ≫ (ihom B).map q)).toFunctor.map α)
      ((hoFunctor.map ((ihom A).map q ≫ (pre k).app Y)).toFunctor.map α) := by
    rw [(pre k).naturality q]
  exact (normalizedVertexHomMap_heq _ _ _ α).trans
    (hm.trans (normalizedVertexHomMap_heq _ _ _ α).symm)

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
