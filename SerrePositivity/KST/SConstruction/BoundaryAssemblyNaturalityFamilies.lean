module
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedFamily
public import SerrePositivity.KST.SConstruction.InverseMixedFamilyTransport

/-! # 随伴構造射の自然性を構成する二つの合成族
概要：延長を動かす族と逆射を動かす族は共通の中間選択で厳密に一致する。
方針：混合族の全次数の両端制限と豊穣合成の中間交換則を使う。
規約：中間部分の等号は写像空間への実際の射の等号。
使われ方：構造射の coherent な自然性のパラメーターの貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping

/-- 逆射を固定して Kan 延長の混合選択を合成する族。 -/
def boundaryAssemblyExtensionFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionKanInverseChoices r X ⊗ kanAssemblyMixedChoices r f ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right :=
  (pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app X) ⊗ₘ
    kanAssemblyMixedFamily r f) ≫ pointedMappingComposition _ _ _

/-- Kan 延長を固定して逆射の混合選択を合成する族。 -/
def boundaryAssemblyInverseFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionInverseMixedChoices r f ⊗ kanAssemblyAdjointChoices r Y ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right :=
  (oneDirectionInverseMixedFamily r f ⊗ₘ kanAssemblyAdjointFamily r Y) ≫
    pointedMappingComposition _ _ _

/-- 共通の中間選択を延長側の混合族のパラメーターへ移す。 -/
def boundaryAssemblyExtensionMiddle (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionKanInverseChoices r X ⊗ kanAssemblyAdjointChoices r Y ⟶
      oneDirectionKanInverseChoices r X ⊗ kanAssemblyMixedChoices r f :=
  𝟙 _ ⊗ₘ kanAssemblyMixedFromTarget r f

/-- 共通の中間選択を逆射側の混合族のパラメーターへ移す。 -/
def boundaryAssemblyInverseMiddle (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionKanInverseChoices r X ⊗ kanAssemblyAdjointChoices r Y ⟶
      oneDirectionInverseMixedChoices r f ⊗ kanAssemblyAdjointChoices r Y :=
  oneDirectionInverseMixedFromSource r f ⊗ₘ 𝟙 _

/-- 二つの自然性の合成族は共通の中間選択上で全次数において厳密に一致する。 -/
lemma boundaryAssemblyNaturalityFamilies_middle (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyExtensionMiddle r f ≫ boundaryAssemblyExtensionFamily r f =
      boundaryAssemblyInverseMiddle r f ≫ boundaryAssemblyInverseFamily r f := by
  dsimp only [boundaryAssemblyExtensionMiddle, boundaryAssemblyExtensionFamily,
    boundaryAssemblyInverseMiddle, boundaryAssemblyInverseFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_target]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_source]
  exact (pointedMappingComposition_families_middle _ _ _).symm

/-- 源の同時選択を延長側の自然性族のパラメーターへ移す。 -/
def boundaryAssemblyExtensionSource (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r X ⟶
      oneDirectionKanInverseChoices r X ⊗ kanAssemblyMixedChoices r f :=
  𝟙 _ ⊗ₘ kanAssemblyMixedFromSource r f

/-- 標的の同時選択を逆射側の自然性族のパラメーターへ移す。 -/
def boundaryAssemblyInverseTarget (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r Y ⟶
      oneDirectionInverseMixedChoices r f ⊗ kanAssemblyAdjointChoices r Y :=
  oneDirectionInverseMixedFromTarget r f ⊗ₘ 𝟙 _

/-- 延長側の合成族の源制限は、元の随伴構造射の族の後合成。 -/
lemma boundaryAssemblyNaturalityFamilies_source (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyExtensionSource r f ≫ boundaryAssemblyExtensionFamily r f =
      boundaryKanAssemblyAdjointFamily r X ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map f)).right := by
  dsimp only [boundaryAssemblyExtensionSource, boundaryAssemblyExtensionFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    kanAssemblyMixedFamily_source]
  exact pointedMappingComposition_families_post _ _ _

/-- 逆射側の合成族の標的制限は、元の随伴構造射の族の前合成。 -/
lemma boundaryAssemblyNaturalityFamilies_target (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyInverseTarget r f ≫ boundaryAssemblyInverseFamily r f =
      boundaryKanAssemblyAdjointFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := by
  dsimp only [boundaryAssemblyInverseTarget, boundaryAssemblyInverseFamily]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    oneDirectionInverseMixedFamily_target]
  exact pointedMappingComposition_families_pre _ _ _

end SerrePositivity.KST.SConstruction
