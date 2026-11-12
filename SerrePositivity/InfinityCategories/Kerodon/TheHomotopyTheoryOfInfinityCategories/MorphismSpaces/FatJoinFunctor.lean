module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison

/-!
概要：fat join の二つの変数に関する関手性。
方針：円柱上の直積写像を両端の射と貼り合わせる。
規約：通常の join の直接定義と公開名は変更しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体とセルへの還元。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二つの射が誘導する fat join の円柱の射。
方針：区間成分を恒等として直積を取る。
規約：因子の順序は (A×Δ[1])×B。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の関手性。 -/
def fatJoinCylinderMap {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ (A' ⊗ (Δ[1] : SSet.{u})) ⊗ B' :=
  (f ▷ (Δ[1] : SSet.{u})) ⊗ₘ g

/-- 概要：円柱の直積写像は零端の包含と可換。
方針：直積の各成分を計算する。
規約：端点の区間成分は零。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせの整合条件。 -/
lemma fatJoinCylinderMap_zero {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    (SSet.ι₀ (X := A) ▷ B) ≫ fatJoinCylinderMap f g =
      (f ⊗ₘ g) ≫ (SSet.ι₀ (X := A') ▷ B') := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：円柱の直積写像は一端の包含と可換。
方針：直積の各成分を計算する。
規約：端点の区間成分は一。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせの整合条件。 -/
lemma fatJoinCylinderMap_one {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    (SSet.ι₁ (X := A) ▷ B) ≫ fatJoinCylinderMap f g =
      (f ⊗ₘ g) ≫ (SSet.ι₁ (X := A') ▷ B') := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：二つの単体集合の射から誘導される fat join の射。
方針：円柱の直積写像と左右の包含の合成を貼り合わせる。
規約：任意の単体集合の射を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の自然性。 -/
noncomputable def fatJoinMap {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A' B' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A' B') (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A' B')
    (fatJoinCylinderMap f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A' B')
    (by rw [← Category.assoc, fatJoinCylinderMap_zero, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero, ← Category.assoc, tensorHom_fst, Category.assoc])
    (by rw [← Category.assoc, fatJoinCylinderMap_one, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one, ← Category.assoc, tensorHom_snd, Category.assoc])

/-- 概要：fat join の誘導射の円柱上の制限。
方針：貼り合わせの円柱上の計算を使う。
規約：因子の順序は既存の円柱と同じ。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手性の計算。 -/
lemma fatJoinCylinder_map {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ≫ fatJoinMap f g =
      fatJoinCylinderMap f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A' B' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

/-- 概要：fat join の誘導射の左因子上の制限。
方針：貼り合わせの左包含上の計算を使う。
規約：左因子を f で写す。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手性の計算。 -/
lemma fatJoinInl_map {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ≫ fatJoinMap f g = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A' B' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：fat join の誘導射の右因子上の制限。
方針：貼り合わせの右包含上の計算を使う。
規約：右因子を g で写す。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手性の計算。 -/
lemma fatJoinInr_map {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ≫ fatJoinMap f g = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A' B' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：fat join の恒等射からの誘導射は恒等射。
方針：円柱と左右の因子上で比較する。
規約：全ての次数での厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手性。 -/
lemma fatJoinMap_id (A B : SSet.{u}) : fatJoinMap (𝟙 A) (𝟙 B) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [fatJoinCylinder_map, Category.comp_id]
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
  · rw [fatJoinInl_map, Category.comp_id, Category.id_comp]
  · rw [fatJoinInr_map, Category.comp_id, Category.id_comp]

/-- 概要：fat join の誘導射は合成を保つ。
方針：円柱と両因子上で直積写像の合成を比較する。
規約：各因子で同じ順序に合成する。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの貼り合わせ。 -/
lemma fatJoinMap_comp {A A' A'' B B' B'' : SSet.{u}}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    fatJoinMap f g ≫ fatJoinMap f' g' = fatJoinMap (f ≫ f') (g ≫ g') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, fatJoinCylinder_map,
      fatJoinCylinder_map, ← Category.assoc]
    rfl
  · rw [← Category.assoc, fatJoinInl_map, Category.assoc, fatJoinInl_map,
      fatJoinInl_map, ← Category.assoc]
  · rw [← Category.assoc, fatJoinInr_map, Category.assoc, fatJoinInr_map,
      fatJoinInr_map, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
