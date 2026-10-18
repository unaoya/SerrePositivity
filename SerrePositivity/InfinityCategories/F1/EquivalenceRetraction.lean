module

public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：単射な圏同値の厳密なレトラクションと、左右の逆による同値の判定。
方針：逆の単位同型を単射に沿って厳密化し、二つの逆を可逆二胞体で比較する。
規約：quasicategory の同値は関手単体集合内の可逆二胞体で扱う。
使われ方：Kerodon §4.5.1、Corollary 4.5.3.24、固定図式の比較の逆の選択。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単射な quasicategory の同値には厳密な左逆がある。
方針：選んだ逆の単位同型を、単射に沿う関手の延長で等式にする。
規約：左逆との合成は射の等式として成立する。
使われ方：Kerodon Corollary 4.5.3.24、固定端点の図式比較のレトラクション。 -/
lemma IsQCatEquivalence.exists_strict_retraction {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} [Mono f]
    (hf : IsQCatEquivalence f) : ∃ r : B ⟶ A, f ≫ r = 𝟙 A := by
  exact exists_extension_of_functorIso f hf.choose.inv (𝟙 A) hf.choose.homInvIso

/-- 概要：厳密な左逆と可逆二胞体による右逆を持つ射は圏同値。
方針：右逆に左逆を後合成して両者を同型にし、左逆の余単位を得る。
規約：二つの逆の一致や射の単射性は要求しない。
使われ方：Kerodon §4.5.1、区間模型の比較の厳密な左逆からの同値判定。 -/
lemma isQCatEquivalence_of_retraction_of_rightInverseIso {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (f : A ⟶ B) (r b : B ⟶ A)
    (hr : f ≫ r = 𝟙 A) (hb : FunctorIso (b ≫ f) (𝟙 B)) :
    IsQCatEquivalence f := by
  have hbr : FunctorIso b r := by
    simpa only [Category.assoc, hr, Category.comp_id, Category.id_comp] using
      FunctorIso.postcomp hb r
  refine ⟨r, ⟨?_⟩, ⟨FunctorIso.postcomp hbr.symm f ≪≫ hb⟩⟩
  rw [hr]

end SerrePositivity.InfinityCategories
