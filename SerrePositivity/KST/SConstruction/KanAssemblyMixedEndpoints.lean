module
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedWhiskering

/-! # 合成入力における混合延長の端点
概要：二本の入力の射に沿う比較を同じ合成入力の選択空間へ移す。
方針：延長空間の射影で前後合成を計算し、厳密な関手法則を使う。
規約：元の選択空間の全高次単体を保つ。
使われ方：自然性ホモトピーの合成を表す三角形の境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping

/-- 源の選択を二回後合成することと、合成入力で移すことは一致する。 -/
lemma kanAssemblyMixedPost_source (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedFromSource r f ≫ kanAssemblyMixedPost r f g =
      kanAssemblyMixedFromSource r (f ≫ g) := by
  apply pullback.hom_ext
  · dsimp only [kanAssemblyMixedFromSource, kanAssemblyMixedPost]
    rw [Category.assoc, pointedExtensionTransport_projection,
      ← Category.assoc, pointedExtensionTransport_projection, Category.assoc,
      pointedMappingTransport_comp, pointedExtensionTransport_projection,
      Category.id_comp, ← CategoryTheory.Functor.map_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 標的の選択を二回前合成することと、合成入力で移すことは一致する。 -/
lemma kanAssemblyMixedPre_target (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedFromTarget r g ≫ kanAssemblyMixedPre r f g =
      kanAssemblyMixedFromTarget r (f ≫ g) := by
  apply pullback.hom_ext
  · dsimp only [kanAssemblyMixedFromTarget, kanAssemblyMixedPre]
    rw [Category.assoc, pointedExtensionTransport_projection,
      ← Category.assoc, pointedExtensionTransport_projection, Category.assoc,
      pointedMappingTransport_comp, pointedExtensionTransport_projection,
      Category.id_comp, ← CategoryTheory.Functor.map_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 中間の入力の選択を前後に移す二つの射は厳密に一致する。 -/
lemma kanAssemblyMixed_middle (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedFromTarget r f ≫ kanAssemblyMixedPost r f g =
      kanAssemblyMixedFromSource r g ≫ kanAssemblyMixedPre r f g := by
  apply pullback.hom_ext
  · dsimp only [kanAssemblyMixedFromSource, kanAssemblyMixedFromTarget,
      kanAssemblyMixedPost, kanAssemblyMixedPre]
    simp only [Category.assoc, pointedExtensionTransport_projection]
    rw [← Category.assoc, pointedExtensionTransport_projection, Category.assoc,
      pointedMappingTransport_comp]
    rw [← Category.assoc, pointedExtensionTransport_projection, Category.assoc,
      pointedMappingTransport_comp]
    simp only [Category.id_comp, Category.comp_id]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.SConstruction
