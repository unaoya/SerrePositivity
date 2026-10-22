module

public import SerrePositivity.InfinityCategories.Core.FatJoinTensorDesc

/-!
概要：右パラメータ付きの fat join 上の射を、円柱と両端への制限で検出する。
方針：パラメータを内部 Hom へ移し、元の二段の pushout の外延性を使う。
規約：充填性は不要。元の全パラメータを保持する。
使われ方：fat 錐の円柱表示の一意性と逆比較の自然性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全パラメータを保つ fat join 上の射は円柱と両端で一意に決まる。 -/
lemma fatJoinTensorRight_hom_ext {A B T X : SSet.{u}} {G H : fatJoin A B ⊗ T ⟶ X}
    (hC : (fatJoinCylinder A B ▷ T) ≫ G = (fatJoinCylinder A B ▷ T) ≫ H)
    (hL : (fatJoinInl A B ▷ T) ≫ G = (fatJoinInl A B ▷ T) ≫ H)
    (hR : (fatJoinInr A B ▷ T) ≫ G = (fatJoinInr A B ▷ T) ≫ H) : G = H := by
  have h : curryTensorRight G = curryTensorRight H := by
    apply fatJoin_hom_ext
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hC]
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hL]
    · rw [← curryTensorRight_natural_left, ← curryTensorRight_natural_left, hR]
  have hh := congrArg (fun q ↦ uncurryTensorRight q) h
  simpa only [uncurryTensorRight_curryTensorRight] using hh

end SerrePositivity.InfinityCategories
