module
public import SerrePositivity.KST.SConstruction.AssemblyMixedFamilyWhiskering
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityFamilies

/-! # 因子合成族の入力の前後合成
概要：合成入力への移送で得る外側の因子族を写像空間の前後合成と同定する。
方針：混合評価族の全次数の可換性と豊穣合成の自然性を使う。
規約：パラメーター空間からの射の等号として保持する。
使われ方：因子の合成三角形の外側の辺を元の自然性へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping

/-- 延長側の合成族の後合成は合成入力への混合延長移送。 -/
lemma boundaryAssemblyExtensionFamily_post (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝟙 (oneDirectionKanInverseChoices r X) ⊗ₘ kanAssemblyMixedPost r f g) ≫
        boundaryAssemblyExtensionFamily r (f ≫ g) =
      boundaryAssemblyExtensionFamily r f ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map g)).right := by
  dsimp only [boundaryAssemblyExtensionFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_post]
  exact pointedMappingComposition_families_post _ _ _

/-- 逆射側の合成族の前合成は合成入力への混合逆射移送。 -/
lemma boundaryAssemblyInverseFamily_pre (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (oneDirectionInverseMixedPre r f g ⊗ₘ 𝟙 (kanAssemblyAdjointChoices r Z)) ≫
        boundaryAssemblyInverseFamily r (f ≫ g) =
      boundaryAssemblyInverseFamily r g ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Z)).right := by
  dsimp only [boundaryAssemblyInverseFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_pre]
  exact pointedMappingComposition_families_pre _ _ _

end SerrePositivity.KST.SConstruction
