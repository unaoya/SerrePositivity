module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction

/-!
概要：パラメータ付き adjunct 対応の二変数の自然性。
方針：単位による adjunct の公式から二胞体の合成との整合を示す。
規約：写像空間の同値自体は本ファイルでは主張しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、HTT §5.2 の写像空間の特徴づけの準備。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：adjunct 対応は終域側の二胞体の合成に自然。
方針：単位による公式と右 whiskering の合成保存を使う。
規約：任意の双圏で成り立つ補助補題。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の自然性。 -/
lemma bicategoryAdjunct_naturality_right {B : Type u} [Bicategory.{w, v} B]
    {a b c : B} {l : b ⟶ c} {r : c ⟶ b}
    (adj : Bicategory.Adjunction l r) {g : a ⟶ b} {h h' : a ⟶ c}
    (α : g ≫ l ⟶ h) (β : h ⟶ h') :
    adj.homEquiv₂ (α ≫ β) = adj.homEquiv₂ α ≫ β ▷ r := by
  simp [Bicategory.Adjunction.homEquiv₂, Category.assoc]

/-- 概要：adjunct 対応は始域側の二胞体の合成に反変自然。
方針：結合子の自然性・交換則・右単位子の自然性を使う。
規約：二胞体の可逆性を仮定しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の自然性。 -/
lemma bicategoryAdjunct_naturality_left {B : Type u} [Bicategory.{w, v} B]
    {a b c : B} {l : b ⟶ c} {r : c ⟶ b}
    (adj : Bicategory.Adjunction l r) {g g' : a ⟶ b} {h : a ⟶ c}
    (γ : g' ⟶ g) (α : g ≫ l ⟶ h) :
    adj.homEquiv₂ (γ ▷ l ≫ α) = γ ≫ adj.homEquiv₂ α := by
  simp only [Bicategory.Adjunction.homEquiv₂, Equiv.coe_fn_mk, Bicategory.comp_whiskerRight]
  rw [← Bicategory.associator_inv_naturality_left_assoc]
  rw [Bicategory.whisker_exchange_assoc]
  rw [← Bicategory.rightUnitor_inv_naturality_assoc]

/-- 概要：adjunct 対応はパラメータの一胞体による前合成と整合する。
方針：単位の公式を展開し、双圏の結合子・単位子の coherence を使う。
規約：非厳密な双圏でも使えるよう結合子を明記する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ自然性。 -/
lemma bicategoryAdjunct_whiskerLeft {B : Type u} [Bicategory.{w, v} B]
    {a b c d : B} {l : b ⟶ c} {r : c ⟶ b}
    (adj : Bicategory.Adjunction l r) (i : d ⟶ a) {g : a ⟶ b} {h : a ⟶ c}
    (α : g ≫ l ⟶ h) :
    adj.homEquiv₂ ((Bicategory.associator i g l).hom ≫ i ◁ α) =
      i ◁ adj.homEquiv₂ α ≫ (Bicategory.associator i h r).inv := by
  dsimp [Bicategory.Adjunction.homEquiv₂]
  bicategory

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

namespace QCatAdjunction

/-- 概要：h Fun に表示した adjunct 対応の終域変数に関する自然性。
方針：双圏の自然性を二胞体の表示同値で写す。
規約：任意のパラメータ Z と、V から V′ への任意の二胞体。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付きの自然性。 -/
lemma homEquiv_naturality_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (U : Z ⟶ X) (V V' : Z ⟶ Y)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (U ≫ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V') :
    a.homEquiv U V' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (α ≫ β)) =
      a.homEquiv U V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (β ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) := by
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U (V' ≫ G))
    (bicategoryAdjunct_naturality_right a α β)

/-- 概要：h Fun に表示した adjunct 対応の始域変数に関する自然性。
方針：双圏の自然性を二胞体の表示同値で写す。
規約：任意のパラメータ Z と、U′ から U への任意の二胞体。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付きの自然性。 -/
lemma homEquiv_naturality_left {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (U U' : Z ⟶ X) (V : Z ⟶ Y)
    (γ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap U) (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (U ≫ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap V) :
    a.homEquiv U' V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (γ ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≫ α)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ γ ≫ a.homEquiv U V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) := by
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' (V ≫ G))
    (bicategoryAdjunct_naturality_left a γ α)

end QCatAdjunction
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
