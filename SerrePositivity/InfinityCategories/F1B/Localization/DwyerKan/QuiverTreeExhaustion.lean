module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreePathLabel

/-!
# 薄い自由 groupoid の全生成辺は全域木に属する

概要：自由 groupoid が薄ければ生成辺は木の正逆どちらかの向きに属する。
方針：根からの木の射で任意の射を表示し、整数群の検出表現を適用する。
規約：一般補題の薄さは実際の被覆では既存の証明を代入する。
使われ方：根付き被覆を木として扱う。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]

lemma labelValue_eq_one {x y : Quiver.FreeGroupoid Q} (f : x ⟶ y) : labelValue T f = 1 := by
  have hf : f = inv (rootHom T x.as) ≫ rootHom T y.as := Subsingleton.elim _ _
  rw [hf, labelValue_comp, labelValue_inv, rootHom_label, rootHom_label, inv_one, mul_one]

lemma every_edge_in_tree {x y : Q} (f : x ⟶ y) : edgeInTree T f := by
  classical
  by_contra hn
  have h := labelValue_eq_one T ((Quiver.FreeGroupoid.of Q).map f)
  rw [labelValue_generator] at h
  change (if edgeInTree T f then 1 else Multiplicative.ofAdd (1 : ℤ)) = 1 at h
  rw [ite_eq_right hn] at h
  exact one_ne_zero (ofAdd_eq_one.mp h)

end SerrePositivity.EInfinity.Hammock.QuiverTree
