module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：単射な圏同値の厳密なレトラクションと、左右の逆による同値の判定。
方針：逆の単位同型を単射に沿って厳密化し、二つの逆を可逆二胞体で比較する。
規約：quasicategory の同値は関手単体集合内の可逆二胞体で扱う。
使われ方：Kerodon §4.5.1（Tag 01DQ）、Corollary 4.5.3.24（Tag 02VM）、固定図式の比較の逆の選択。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射な quasicategory の同値には厳密な左逆がある。
方針：選んだ逆の単位同型を、単射に沿う関手の延長で等式にする。
規約：左逆との合成は射の等式として成立する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM）、固定端点の図式比較のレトラクション。 -/
lemma IsQCatEquivalence.exists_strict_retraction {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) : ∃ r : B ⟶ A, f ≫ r = 𝟙 A := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_extension_of_functorIso f hf.choose.inv (𝟙 A) hf.choose.homInvIso

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (exists_strict_retraction)


/-- 概要：厳密な左逆と可逆二胞体による右逆を持つ射は圏同値。
方針：右逆に左逆を後合成して両者を同型にし、左逆の余単位を得る。
規約：二つの逆の一致や射の単射性は要求しない。
使われ方：Kerodon §4.5.1（Tag 01DQ）、区間模型の比較の厳密な左逆からの同値判定。 -/
lemma isQCatEquivalence_of_retraction_of_rightInverseIso {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (f : A ⟶ B) (r b : B ⟶ A)
    (hr : f ≫ r = 𝟙 A) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ f) (𝟙 B)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have hbr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b r := by
    simpa only [Category.assoc, hr, Category.comp_id, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hb r
  refine ⟨r, ⟨?_⟩, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp hbr.symm f ≪≫ hb⟩⟩
  rw [hr]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
