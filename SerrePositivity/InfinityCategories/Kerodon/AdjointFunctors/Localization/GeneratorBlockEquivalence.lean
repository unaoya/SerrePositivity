module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockNormalize

/-!
# 元の自由射列の交互標準形の存在と一意性

概要：元の射列と空でない単色ブロックの交互標準形は互いに一意に対応する。
方針：単色ブロックの追加を保つ正規化から、標準形の復元の逆を証明する。
規約：元の端点・全生成矢・恒等文字を保持した全単射。
使われ方：自由積と元の hammock の行の交互分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

lemma normalize_flatten {X : C} {c : Option Bool} {Y : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Form W X c Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten W N) = ⟨c, N⟩ := by
  induction N with
  | nil => rfl
  | snoc initial c block positive uniform alternate ih =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize_appendBlock W initial c block uniform alternate ih).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendBlock_positive W initial c block positive uniform alternate)

lemma normalize_flattenNormal {X Y : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N) = N := by
  rcases N with ⟨c, N⟩
  exact normalize_flatten W N

def equivalence (X Y : C) : Quiver.Path X Y ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W
  left_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_normalize W
  right_inv := normalize_flattenNormal W

lemma flatten_injective (X Y : C) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y → Quiver.Path X Y) :=
  (equivalence W X Y).symm.injective

lemma normal_eq_iff {X Y : C} (N M : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) :
    N = M ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W M :=
  (flatten_injective W X Y).eq_iff.symm

lemma existsUnique_normal {X Y : C} (p : Quiver.Path X Y) :
    ∃! N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N = p := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W p, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_normalize W p, ?_⟩
  intro N hN
  exact (flatten_injective W X Y) (hN.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_normalize W p).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence
