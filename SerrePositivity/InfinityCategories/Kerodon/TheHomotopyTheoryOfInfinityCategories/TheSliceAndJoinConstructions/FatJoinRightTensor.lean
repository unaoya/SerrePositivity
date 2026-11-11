module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorDesc
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorExt

/-! # Fat join の右因子とパラメーター

概要：fat join とパラメーターの直積を、右因子にパラメーターを持つ fat join へ写す。
方針：両因子と円柱の射を二段の pushout で貼る。
規約：左因子の図式を固定する。使われ方：余錐の族の curry と uncurry。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：右因子のパラメーターを円柱の右成分に並べる。
方針：直積の成分を直接並べ替える。
規約：区間の向きは保つ。使われ方：右因子の直積比較の円柱。 -/
def stableFatJoinRightCylinderShuffle (A B P : SSet.{u}) :
    ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ P ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ (B ⊗ P) where
  app _ := ↾fun z => (z.1.1, (z.1.2, z.2))

/-- 概要：fat join とパラメーターの直積を右因子の直積へ写す。
方針：左因子でパラメーターを忘れ、右因子と円柱には残して貼る。
規約：左の図式は厳密に固定する。使われ方：太い coslice の普遍族。 -/
def stableFatJoinTensorRight (A B P : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⊗ P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDescTensorRight (fst A P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A (B ⊗ P))
    (stableFatJoinRightCylinderShuffle A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P))
    (by
      have he : ((SSet.ι₀ (X := A) ▷ B) ▷ P) ≫ stableFatJoinRightCylinderShuffle A B P =
          (α_ A B P).hom ≫ (SSet.ι₀ (X := A) ▷ (B ⊗ P)) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero]
      rfl)
    (by
      have he : ((SSet.ι₁ (X := A) ▷ B) ▷ P) ≫ stableFatJoinRightCylinderShuffle A B P =
          (α_ A B P).hom ≫ (SSet.ι₁ (X := A) ▷ (B ⊗ P)) := rfl
      rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one]
      rfl)

/-- 概要：右直積比較は左包含上でパラメーターを忘れる。
方針：貼り合わせの左因子での計算。
規約：厳密な等式。使われ方：余錐の固定図式の条件。 -/
lemma stableFatJoinTensorRight_inl (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ P) ≫ stableFatJoinTensorRight A B P =
      fst A P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_descTensorRight _ _ _ _ _

/-- 概要：右直積比較は右包含上でパラメーターを保持する。
方針：貼り合わせの右因子での計算。
規約：厳密な等式。使われ方：太い coslice の頂点の評価。 -/
lemma stableFatJoinTensorRight_inr (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P) ≫ stableFatJoinTensorRight A B P =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A (B ⊗ P) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_descTensorRight _ _ _ _ _

/-- 概要：右直積比較は円柱上で成分を並べ替える。
方針：貼り合わせの円柱上での計算。
規約：区間の座標を保持する。使われ方：curry と uncurry の逆則。 -/
lemma stableFatJoinTensorRight_cylinder (A B P : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P) ≫ stableFatJoinTensorRight A B P =
      stableFatJoinRightCylinderShuffle A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_descTensorRight _ _ _ _ _

/-- 概要：右直積比較はパラメーターの射に自然。
方針：円柱と両因子で比較する。
規約：fat join の因子を固定する。使われ方：普遍余錐の族の自然性。 -/
lemma stableFatJoinTensorRight_naturality {P Q : SSet.{u}} (f : P ⟶ Q) (A B : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ◁ f) ≫ stableFatJoinTensorRight A B Q =
      stableFatJoinTensorRight A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 A) (B ◁ f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_tensorRight_hom_ext
  · have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ◁ f) =
        (((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ Q) := rfl
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P), hs]
    simp only [Category.assoc]
    rw [stableFatJoinTensorRight_cylinder,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P), stableFatJoinTensorRight_cylinder]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map]
    rfl
  · have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ P) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ◁ f) =
        (A ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ Q) := rfl
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ P), hs]
    simp only [Category.assoc]
    rw [stableFatJoinTensorRight_inl, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ P),
      stableFatJoinTensorRight_inl]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp]
    rfl
  · have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ◁ f) =
        (B ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ Q) := rfl
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P), hs]
    simp only [Category.assoc]
    rw [stableFatJoinTensorRight_inr, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P),
      stableFatJoinTensorRight_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map]

/-- 概要：右直積比較の後でパラメーターを忘れると元の射影となる。
方針：円柱と両因子の射影を比較する。
規約：パラメーターは任意。使われ方：太い coslice の普遍性の単位則。 -/
lemma stableFatJoinTensorRight_projection (A B P : SSet.{u}) :
    stableFatJoinTensorRight A B P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 A) (fst B P) = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B) P := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_tensorRight_hom_ext
  · rw [← Category.assoc, stableFatJoinTensorRight_cylinder]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map]
    rfl
  · rw [← Category.assoc, stableFatJoinTensorRight_inl]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp]
    rfl
  · rw [← Category.assoc, stableFatJoinTensorRight_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
