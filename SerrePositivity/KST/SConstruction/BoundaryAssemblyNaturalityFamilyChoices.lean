module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityKan
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

/-! # 自然性の Kan パラメーター族の延長の全選択
概要：二重円筒上の族を Kan 空間へ延長する選び方も可縮な空間で制御する。
方針：基点を要求しない anodyne 延長の選択空間を使う。
規約：任意の選択でも両端の全パラメーターの回収を厳密に保つ。
使われ方：入力の射列に沿う自然性の族の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 自然性の二重円筒の族を厳密に延長する全選択。 -/
def boundaryAssemblyNaturalityFamilyChoices (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} :=
  anodyneExtensionChoices (boundaryAssemblyNaturalityParameterUnit r f)
    (boundaryAssemblyNaturalityCylinderFamily r f)

/-- 自然性の族の延長の全選択空間は可縮 Kan。 -/
lemma boundaryAssemblyNaturalityFamilyChoices_isContractibleKan (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (boundaryAssemblyNaturalityFamilyChoices r f) :=
  anodyneExtensionChoices_isContractibleKan _
    (AnodyneKanReplacement.unit_anodyne (boundaryAssemblyNaturalityCylinder r f)) _

/-- 延長の選択の既存部分を保つ高次の補完。 -/
lemma boundaryAssemblyNaturalityFamilyChoices_relative_lifting (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ boundaryAssemblyNaturalityFamilyChoices r f) :
    ∃ b : T ⟶ boundaryAssemblyNaturalityFamilyChoices r f, j ≫ b = a :=
  anodyneExtensionChoices_relative_lifting _
    (AnodyneKanReplacement.unit_anodyne (boundaryAssemblyNaturalityCylinder r f)) _ j a

/-- 任意の延長選択が与える実際の Kan パラメーター族。 -/
def boundaryAssemblyNaturalityFamilyAt (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌) :
    boundaryAssemblyNaturalityParameters r f ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := anodyneExtensionAt _ _ v

/-- 全ての延長選択で二重円筒の元の族を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamilyAt_unit (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌) :
    boundaryAssemblyNaturalityParameterUnit r f ≫ boundaryAssemblyNaturalityFamilyAt r f v =
      boundaryAssemblyNaturalityCylinderFamily r f := anodyneExtensionAt_fac _ _ v

/-- 任意の延長選択で、源の全ての構造射選択の族を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamilyAt_source (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌) :
    boundaryAssemblyNaturalitySource r f ≫ boundaryAssemblyNaturalityFamilyAt r f v =
      boundaryKanAssemblyAdjointFamily r X ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map f)).right := by
  rw [boundaryAssemblyNaturalitySource, Category.assoc, boundaryAssemblyNaturalityFamilyAt_unit]
  exact boundaryAssemblyNaturalityCylinderFamily_source r f

/-- 任意の延長選択で、標的の全ての構造射選択の族を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamilyAt_target (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (boundaryAssemblyNaturalityFamilyChoices r f) _⦋0⦌) :
    boundaryAssemblyNaturalityTarget r f ≫ boundaryAssemblyNaturalityFamilyAt r f v =
      boundaryKanAssemblyAdjointFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := by
  rw [boundaryAssemblyNaturalityTarget, Category.assoc, boundaryAssemblyNaturalityFamilyAt_unit]
  exact boundaryAssemblyNaturalityCylinderFamily_target r f

end SerrePositivity.KST.SConstruction
