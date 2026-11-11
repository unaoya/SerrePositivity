module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionConeUniversal

/-!
概要：fat join の右因子へ直積のパラメータを移す比較。
方針：右因子と円柱ではパラメータを保持し、左因子では忘れて貼り合わせる。
規約：通常の joinTensorRight と同じ向きの射を与える。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の錐の族の模型の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の円柱のパラメータを右因子に移す並べ替え。
方針：直積の成分を直接並べ替える。
規約：入力は ((A×区間)×B)×P。
使われ方：Kerodon §4.6.6（Tag 04HY） の右因子の直積の比較の円柱。 -/
def fatJoinTensorRightCylinderShuffle (A B P : SSet.{u}) :
    ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ P ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ (B ⊗ P) where
  app _ := ↾fun z ↦ (z.1.1, (z.1.2, z.2))

/-- 概要：右のパラメータを fat join の右因子へ移す。
方針：左右の包含と並べ替えた円柱を、パラメータ付きの普遍性で貼る。
規約：左因子上ではパラメータを忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の coslice の切断の族への比較。 -/
noncomputable def fatJoinTensorRight (A B P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⊗ P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDescTensorRight (fst A P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A (B ⊗ P))
    (fatJoinTensorRightCylinderShuffle A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P))
    (by
      have he : ((SSet.ι₀ (X := A) ▷ B) ▷ P) ≫
          fatJoinTensorRightCylinderShuffle A B P =
          (α_ A B P).hom ≫ (SSet.ι₀ (X := A) ▷ (B ⊗ P)) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero]
      rfl)
    (by
      have he : ((SSet.ι₁ (X := A) ▷ B) ▷ P) ≫
          fatJoinTensorRightCylinderShuffle A B P =
          (α_ A B P).hom ≫ (SSet.ι₁ (X := A) ▷ (B ⊗ P)) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one]
      rfl)

/-- 概要：fat join の右直積比較は左包含上でパラメータを忘れる。
方針：貼り合わせの左因子の計算を使う。
規約：左右とパラメータの三つの因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射の固定頂点の条件。 -/
lemma fatJoinTensorRight_inl (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ P) ≫ fatJoinTensorRight A B P = fst A P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_descTensorRight _ _ _ _ _

/-- 概要：fat join の右直積比較は右包含上で両成分を保持する。
方針：貼り合わせの右因子の計算を使う。
規約：パラメータを右図式の中へ移す。
使われ方：Kerodon §4.6.6（Tag 04HY） の比較射の固定図式の条件。 -/
lemma fatJoinTensorRight_inr (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P) ≫ fatJoinTensorRight A B P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_descTensorRight _ _ _ _ _

/-- 概要：fat join の右直積比較は円柱のパラメータを右因子に移す。
方針：貼り合わせの円柱の計算を使う。
規約：join の区間の値を変えない。
使われ方：Kerodon §4.6.6（Tag 04HY） の通常の join の比較との整合性。 -/
lemma fatJoinTensorRight_cylinder (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P) ≫ fatJoinTensorRight A B P =
      fatJoinTensorRightCylinderShuffle A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_descTensorRight _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
