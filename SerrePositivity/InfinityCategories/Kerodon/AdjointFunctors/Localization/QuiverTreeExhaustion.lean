module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreePathLabel

/-!
# 薄い自由 groupoid の全生成辺は全域木に属する

概要：自由 groupoid が薄ければ生成辺は木の正逆どちらかの向きに属する。
方針：根からの木の射で任意の射を表示し、整数群の検出表現を適用する。
規約：一般補題の薄さは実際の被覆では既存の証明を代入する。
使われ方：根付き被覆を木として扱う。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma labelValue_eq_one {x y : Quiver.FreeGroupoid Q} (f : x ⟶ y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.labelValue T f = 1 := by
  have hf : f = inv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHom T x.as) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHom T y.as := Subsingleton.elim _ _
  rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.labelValue_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.labelValue_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHom_label, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHom_label, inv_one, mul_one]

lemma every_edge_in_tree {x y : Q} (f : x ⟶ y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.edgeInTree T f := by
  classical
  by_contra hn
  have h := labelValue_eq_one T ((Quiver.FreeGroupoid.of Q).map f)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.labelValue_generator] at h
  change (if _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector.edgeInTree T f then 1 else Multiplicative.ofAdd (1 : ℤ)) = 1 at h
  rw [ite_eq_right hn] at h
  exact one_ne_zero (ofAdd_eq_one.mp h)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
