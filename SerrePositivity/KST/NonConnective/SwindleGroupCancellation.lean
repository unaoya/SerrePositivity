module

public import Mathlib.Algebra.Group.Hom.Basic

/-!
概要：加法性と swindle の同型側から、同じ群の実消滅を導く消去補題。
方針：指定した同じ二つの群準同型の値を比較し、群の消去律を適用する。
規約：加法性の等式そのものはこの補題で証明したと扱わない。
使われ方：BGT Lem. 9.4 の固定 BF K の整数 π への適用。
-/

@[expose] public section
universe u v
namespace SerrePositivity.KST.NonConnective

/-- 加法的な swindle の二つの実自己作用が等しければ、全ての元は単位。 -/
lemma swindleGroup_eq_one {G : Type u} [Group G] (s t : G →* G)
    (ha : ∀ x, s x = x * t x) (he : s = t) (x : G) : x = 1 := by
  have hx : x * t x = 1 * t x := (ha x).symm.trans
    ((DFunLike.congr_fun he x).trans (one_mul (t x)).symm)
  exact mul_right_cancel hx

/-- 同じ swindle の作用による群の実消滅。 -/
lemma swindleGroup_subsingleton {G : Type u} [Group G] (s t : G →* G)
    (ha : ∀ x, s x = x * t x) (he : s = t) : Subsingleton G :=
  ⟨fun x y ↦ (swindleGroup_eq_one s t ha he x).trans (swindleGroup_eq_one s t ha he y).symm⟩

end SerrePositivity.KST.NonConnective
