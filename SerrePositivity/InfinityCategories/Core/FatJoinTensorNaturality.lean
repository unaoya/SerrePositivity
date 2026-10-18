module

public import SerrePositivity.InfinityCategories.Core.FatJoinTensorExt

/-!
概要：fat join と直積の比較の自然性と零単体での単位則。
方針：円柱と両因子上で成分の並べ替えを計算する。
規約：右因子を厳密に固定する。
使われ方：Kerodon §4.6.6 の太い slice の curry と uncurry。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join の直積の比較はパラメーターの射に自然。
方針：円柱と左右の因子上で計算する。
規約：A と K は固定する。
使われ方：Kerodon §4.6.6 の太い slice の普遍族の自然性。 -/
lemma fatJoinTensorLeft_naturality {P Q : SSet.{u}} (f : P ⟶ Q) (A K : SSet.{u}) :
    (f ▷ fatJoin A K) ≫ fatJoinTensorLeft Q A K =
      fatJoinTensorLeft P A K ≫ fatJoinMap (f ▷ A) (𝟙 K) := by
  apply fatJoin_tensorLeft_hom_ext
  · have hs : (P ◁ fatJoinCylinder A K) ≫ (f ▷ fatJoin A K) =
        (f ▷ ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K)) ≫ (Q ◁ fatJoinCylinder A K) := rfl
    rw [← Category.assoc (P ◁ fatJoinCylinder A K), hs]
    simp only [Category.assoc]
    rw [fatJoinTensorLeft_cylinder, ← Category.assoc (P ◁ fatJoinCylinder A K),
      fatJoinTensorLeft_cylinder]
    simp only [Category.assoc]
    rw [fatJoinCylinder_map]
    rfl
  · have hs : (P ◁ fatJoinInl A K) ≫ (f ▷ fatJoin A K) =
        (f ▷ A) ≫ (Q ◁ fatJoinInl A K) := rfl
    rw [← Category.assoc (P ◁ fatJoinInl A K), hs]
    simp only [Category.assoc]
    rw [fatJoinTensorLeft_inl, ← Category.assoc (P ◁ fatJoinInl A K),
      fatJoinTensorLeft_inl, fatJoinInl_map]
  · have hs : (P ◁ fatJoinInr A K) ≫ (f ▷ fatJoin A K) =
        (f ▷ K) ≫ (Q ◁ fatJoinInr A K) := rfl
    rw [← Category.assoc (P ◁ fatJoinInr A K), hs]
    simp only [Category.assoc]
    rw [fatJoinTensorLeft_inr, ← Category.assoc (P ◁ fatJoinInr A K), fatJoinTensorLeft_inr]
    simp only [Category.assoc, fatJoinInr_map, Category.id_comp]
    rfl

/-- 概要：fat join の直積の比較後に左因子のパラメーターを忘れると元の射影。
方針：円柱と両因子の射影を比較する。
規約：パラメーター P は任意。
使われ方：Kerodon §4.6.6 の太い slice の普遍性の単位則。 -/
lemma fatJoinTensorLeft_projection (P A K : SSet.{u}) :
    fatJoinTensorLeft P A K ≫
      fatJoinMap (snd P A) (𝟙 K) = snd P (fatJoin A K) := by
  apply fatJoin_tensorLeft_hom_ext
  · rw [← Category.assoc, fatJoinTensorLeft_cylinder]
    simp only [Category.assoc]
    rw [fatJoinCylinder_map]
    rfl
  · rw [← Category.assoc, fatJoinTensorLeft_inl, fatJoinInl_map]
    rfl
  · rw [← Category.assoc, fatJoinTensorLeft_inr]
    simp only [Category.assoc, fatJoinInr_map, Category.id_comp]
    rfl

/-- 概要：零単体のパラメーターでの fat join の直積の比較は射影。
方針：一般のパラメーターを忘れる等式の特殊化。
規約：零単体の直積の単位を射影で表す。
使われ方：Kerodon §4.6.6 の太い slice の普遍性の単位則。 -/
lemma fatJoinTensorLeft_unit (A K : SSet.{u}) :
    fatJoinTensorLeft (Δ[0] : SSet.{u}) A K ≫
      fatJoinMap (snd (Δ[0] : SSet.{u}) A) (𝟙 K) = snd Δ[0] (fatJoin A K) :=
  fatJoinTensorLeft_projection Δ[0] A K

end SerrePositivity.InfinityCategories
