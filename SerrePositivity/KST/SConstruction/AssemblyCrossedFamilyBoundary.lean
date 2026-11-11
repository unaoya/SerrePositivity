module
public import SerrePositivity.KST.SConstruction.AssemblyCrossedFamily
public import SerrePositivity.KST.SConstruction.AssemblyMixedFamilyWhiskering
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityFamilies

/-! # 交差する混合評価族の四辺
概要：交差族の四つの制限を元の因子族または合成入力の因子族と同定する。
方針：両端制限、前後合成の自然性と豊穣合成の中間交換を使う。
規約：単体集合への実際の射として等号を保持する。
使われ方：逆射・延長の辺の交換を指定した自然性の合成へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping

/-- 延長の源を固定した辺は最初の逆射族の後合成。 -/
lemma assemblyCrossedFamily_extension_source (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝟙 (oneDirectionInverseMixedChoices r f) ⊗ₘ kanAssemblyMixedFromSource r g) ≫
        assemblyCrossedFamily r f g =
      boundaryAssemblyInverseFamily r f ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map g)).right := by
  dsimp only [assemblyCrossedFamily, boundaryAssemblyInverseFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_source]
  exact pointedMappingComposition_families_post _ _ _

/-- 逆射の標的を固定した辺は次の延長族の前合成。 -/
lemma assemblyCrossedFamily_inverse_target (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (oneDirectionInverseMixedFromTarget r f ⊗ₘ 𝟙 (kanAssemblyMixedChoices r g)) ≫
        assemblyCrossedFamily r f g =
      boundaryAssemblyExtensionFamily r g ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Z)).right := by
  dsimp only [assemblyCrossedFamily, boundaryAssemblyExtensionFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_target]
  exact pointedMappingComposition_families_pre _ _ _

/-- 逆射の源を固定した辺は合成入力の延長族への前合成移送。 -/
lemma assemblyCrossedFamily_inverse_source (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (oneDirectionInverseMixedFromSource r f ⊗ₘ 𝟙 (kanAssemblyMixedChoices r g)) ≫
        assemblyCrossedFamily r f g =
      (𝟙 (oneDirectionKanInverseChoices r X) ⊗ₘ kanAssemblyMixedPre r f g) ≫
        boundaryAssemblyExtensionFamily r (f ≫ g) := by
  dsimp only [assemblyCrossedFamily, boundaryAssemblyExtensionFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_source]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_pre]
  exact pointedMappingComposition_families_middle _ _ _

/-- 延長の標的を固定した辺は合成入力の逆射族への後合成移送。 -/
lemma assemblyCrossedFamily_extension_target (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝟙 (oneDirectionInverseMixedChoices r f) ⊗ₘ kanAssemblyMixedFromTarget r g) ≫
        assemblyCrossedFamily r f g =
      (oneDirectionInverseMixedPost r f g ⊗ₘ 𝟙 (kanAssemblyAdjointChoices r Z)) ≫
        boundaryAssemblyInverseFamily r (f ≫ g) := by
  dsimp only [assemblyCrossedFamily, boundaryAssemblyInverseFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_target]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_post]
  exact (pointedMappingComposition_families_middle _ _ _).symm

end SerrePositivity.KST.SConstruction
