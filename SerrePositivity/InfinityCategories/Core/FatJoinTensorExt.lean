module

public import SerrePositivity.InfinityCategories.Core.FatJoinTensor

/-!
概要：直積を持つ fat join からの射の外延性。
方針：パラメーターを内部 Hom に移して fat join の普遍性を使う。
規約：両因子と円柱上で比較する。
使われ方：Kerodon §4.6.6 の太い slice の普遍性の等式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右パラメーター付き fat join 上の射は円柱と両因子で決まる。
方針：curry した二つの射に fat join の外延性を適用する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.6 のパラメーター付き普遍性。 -/
lemma fatJoin_tensorRight_hom_ext {A K P X : SSet.{u}} {f g : fatJoin A K ⊗ P ⟶ X}
    (hC : (fatJoinCylinder A K ▷ P) ≫ f = (fatJoinCylinder A K ▷ P) ≫ g)
    (hA : (fatJoinInl A K ▷ P) ≫ f = (fatJoinInl A K ▷ P) ≫ g)
    (hK : (fatJoinInr A K ▷ P) ≫ f = (fatJoinInr A K ▷ P) ≫ g) : f = g := by
  have hh : curryTensorRight f = curryTensorRight g := by
    apply fatJoin_hom_ext
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hC]
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hA]
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hK]
  simpa only [uncurryTensorRight_curryTensorRight] using congrArg uncurryTensorRight hh

/-- 概要：左パラメーター付き fat join 上の射は円柱と両因子で決まる。
方針：対称性で右パラメーターに戻す。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.6 の太い slice の普遍族。 -/
lemma fatJoin_tensorLeft_hom_ext {A K P X : SSet.{u}} {f g : P ⊗ fatJoin A K ⟶ X}
    (hC : (P ◁ fatJoinCylinder A K) ≫ f = (P ◁ fatJoinCylinder A K) ≫ g)
    (hA : (P ◁ fatJoinInl A K) ≫ f = (P ◁ fatJoinInl A K) ≫ g)
    (hK : (P ◁ fatJoinInr A K) ≫ f = (P ◁ fatJoinInr A K) ≫ g) : f = g := by
  apply (cancel_epi (β_ (fatJoin A K) P).hom).1
  apply fatJoin_tensorRight_hom_ext
  · change (β_ ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K) P).hom ≫
        (P ◁ fatJoinCylinder A K) ≫ f =
      (β_ ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K) P).hom ≫ (P ◁ fatJoinCylinder A K) ≫ g
    rw [hC]
  · change (β_ A P).hom ≫ (P ◁ fatJoinInl A K) ≫ f =
      (β_ A P).hom ≫ (P ◁ fatJoinInl A K) ≫ g
    rw [hA]
  · change (β_ K P).hom ≫ (P ◁ fatJoinInr A K) ≫ f =
      (β_ K P).hom ≫ (P ◁ fatJoinInr A K) ≫ g
    rw [hK]

end SerrePositivity.InfinityCategories
