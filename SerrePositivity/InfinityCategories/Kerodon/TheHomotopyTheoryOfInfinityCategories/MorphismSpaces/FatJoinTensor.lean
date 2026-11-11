module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorDesc

/-!
概要：fat join の左因子と直積の比較。
方針：パラメーターを左右の因子と円柱上で移し、二段の pushout で貼る。
規約：右因子上ではパラメーターを忘れる。
使われ方：Kerodon §4.6.4（Tag 01KE）・4.6.6（Tag 04HY） の太い slice の普遍性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の因子とパラメーターの順を入れ替える。
方針：直積の成分を直接並べ替える。
規約：入力は (A×K)×P、出力は (P×A)×K。
使われ方：Kerodon §4.6.6（Tag 04HY） の直積の比較の端点。 -/
def fatJoinTensorInputShuffle (P A K : SSet.{u}) : (A ⊗ K) ⊗ P ⟶ (P ⊗ A) ⊗ K where
  app n := ↾fun z ↦ ((z.2, z.1.1), z.1.2)

/-- 概要：fat join の円柱のパラメーターを左因子へ移す。
方針：区間と右因子を保ってパラメーターを先頭へ並べる。
規約：入力は ((A×Δ[1])×K)×P。
使われ方：Kerodon §4.6.6（Tag 04HY） の直積の比較の円柱。 -/
def fatJoinTensorCylinderShuffle (P A K : SSet.{u}) :
    ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K) ⊗ P ⟶ ((P ⊗ A) ⊗ (Δ[1] : SSet.{u})) ⊗ K where
  app n := ↾fun z ↦ (((z.2, z.1.1.1), z.1.1.2), z.1.2)

/-- 概要：右のパラメーターを fat join の左因子へ移す。
方針：左右の因子と並べ替えた円柱をパラメーター付きの pushout で貼る。
規約：右因子のパラメーターは射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice の普遍族。 -/
noncomputable def fatJoinTensorLeftRight (P A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⊗ P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (P ⊗ A) K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDescTensorRight ((β_ A P).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (P ⊗ A) K)
    (fst K P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (P ⊗ A) K)
    (fatJoinTensorCylinderShuffle P A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder (P ⊗ A) K)
    (by
      have he : ((SSet.ι₀ (X := A) ▷ K) ▷ P) ≫ fatJoinTensorCylinderShuffle P A K =
          fatJoinTensorInputShuffle P A K ≫ (SSet.ι₀ (X := P ⊗ A) ▷ K) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero]
      rfl)
    (by
      have he : ((SSet.ι₁ (X := A) ▷ K) ▷ P) ≫ fatJoinTensorCylinderShuffle P A K =
          fatJoinTensorInputShuffle P A K ≫ (SSet.ι₁ (X := P ⊗ A) ▷ K) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one]
      rfl)

/-- 概要：左のパラメーターを fat join の左因子へ移す。
方針：対称性でパラメーターを右へ移し、構成済みの比較を使う。
規約：通常の joinTensorLeft と同じ向き。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice の普遍性。 -/
noncomputable def fatJoinTensorLeft (P A K : SSet.{u}) :
    P ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (P ⊗ A) K :=
  (β_ P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K)).hom ≫ fatJoinTensorLeftRight P A K

/-- 概要：fat join の直積の比較は左因子上で恒等的な包含。
方針：対称性の自然性と貼り合わせの左因子の計算。
規約：パラメーターを左因子に保持する。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍族の左端。 -/
lemma fatJoinTensorLeft_inl (P A K : SSet.{u}) :
    (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K) ≫ fatJoinTensorLeft P A K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (P ⊗ A) K := by
  have hs : (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K) ≫ (β_ P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K)).hom =
      (β_ P A).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ P) := rfl
  rw [fatJoinTensorLeft, ← Category.assoc, hs, Category.assoc]
  rw [fatJoinTensorLeftRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_descTensorRight]
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：fat join の直積の比較は右因子上でパラメーターを忘れる。
方針：対称性の自然性と貼り合わせの右因子の計算。
規約：右因子を厳密に固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の普遍族の固定条件。 -/
lemma fatJoinTensorLeft_inr (P A K : SSet.{u}) :
    (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K) ≫ fatJoinTensorLeft P A K = snd P K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (P ⊗ A) K := by
  have hs : (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K) ≫ (β_ P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K)).hom =
      (β_ P K).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ P) := rfl
  rw [fatJoinTensorLeft, ← Category.assoc, hs, Category.assoc]
  rw [fatJoinTensorLeftRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_descTensorRight]
  rfl

/-- 概要：fat join の直積の比較は円柱の成分を並べ替える。
方針：対称性の自然性と貼り合わせの円柱の計算。
規約：区間の座標は変えない。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice の普遍性の計算。 -/
lemma fatJoinTensorLeft_cylinder (P A K : SSet.{u}) :
    (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K) ≫ fatJoinTensorLeft P A K =
      (β_ P ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K)).hom ≫
        fatJoinTensorCylinderShuffle P A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder (P ⊗ A) K := by
  have hs : (P ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K) ≫ (β_ P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K)).hom =
      (β_ P ((A ⊗ (Δ[1] : SSet.{u})) ⊗ K)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K ▷ P) := rfl
  rw [fatJoinTensorLeft, ← Category.assoc, hs, Category.assoc]
  rw [fatJoinTensorLeftRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_descTensorRight]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
