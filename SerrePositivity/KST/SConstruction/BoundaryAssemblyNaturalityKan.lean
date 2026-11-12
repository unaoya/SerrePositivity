module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityCylinder
public import SerrePositivity.KST.SConstruction.DoubleCylinderContractibility

/-! # 自然性の可縮な Kan パラメーター空間
概要：貼り合わせた二重円筒を Kan 置換し、その上へ元の合成族を厳密に延長する。
方針：円筒の弱可縮性と anodyne 単位に沿う Kan 標的への持ち上げを使う。
規約：全ての元の選択パラメーターで両端を厳密に回収する。
使われ方：構造射の自然性の高次比較と相対境界の充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open Spectra Spectra.PointedMapping Comparison
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 自然性の二重円筒を Kan 置換したパラメーター空間。 -/
def boundaryAssemblyNaturalityParameters (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} :=
  AnodyneKanReplacement.functor.obj (boundaryAssemblyNaturalityCylinder r f)

/-- 貼り合わせた全ての元のパラメーターを Kan 空間へ移す単位。 -/
def boundaryAssemblyNaturalityParameterUnit (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinder r f ⟶ boundaryAssemblyNaturalityParameters r f :=
  AnodyneKanReplacement.unit.app _

/-- 二重円筒の Kan 置換は全ての境界を充填する可縮 Kan 複体。 -/
lemma boundaryAssemblyNaturalityParameters_isContractibleKan (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (boundaryAssemblyNaturalityParameters r f) := by
  have hC := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor (oneDirectionKanInverseChoices_isContractibleKan r X)
    (kanAssemblyAdjointChoices_isContractibleKan r Y)
  have hA := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor (oneDirectionKanInverseChoices_isContractibleKan r X)
    (kanAssemblyMixedChoices_isContractibleKan r f)
  have hB := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.contractibleKan_tensor (oneDirectionInverseMixedChoices_isContractibleKan r f)
    (kanAssemblyAdjointChoices_isContractibleKan r Y)
  let a := hA.nonempty.some
  exact kanReplacement_contractible_of_localized_toUnit
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f)
      (boundaryAssemblyInverseMiddle r f)).app (Opposite.op ⦋0⦌) a)
    (doubleCylinder_toUnit_localized_isIso _ _ hC hA hB)

/-- 自然性の Kan パラメーター空間の全高次比較を相対的に補完できる。 -/
lemma boundaryAssemblyNaturalityParameters_relative_lifting (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ boundaryAssemblyNaturalityParameters r f) :
    ∃ b : T ⟶ boundaryAssemblyNaturalityParameters r f, j ≫ b = a := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).mp
    (boundaryAssemblyNaturalityParameters_isContractibleKan r f)
  have := hc.mem j inferInstance
  let sq : CommSq a j (terminal.from (boundaryAssemblyNaturalityParameters r f))
      (terminal.from T) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 元の貼り合わせた族は Kan パラメーター空間へ厳密に延長できる。 -/
lemma exists_boundaryAssemblyNaturalityFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ∃ F : boundaryAssemblyNaturalityParameters r f ⟶
        (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right,
      boundaryAssemblyNaturalityParameterUnit r f ≫ F = boundaryAssemblyNaturalityCylinderFamily r f := by
  let T := (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
    ((loopBoundaryKanFunctor (r + 1)).obj Y)).right
  have : HasLiftingProperty (boundaryAssemblyNaturalityParameterUnit r f) (terminal.from T) :=
    (AnodyneKanReplacement.unit_anodyne (boundaryAssemblyNaturalityCylinder r f)) _
      ((fibration_iff _).mp (inferInstance : Fibration (terminal.from T)))
  let sq : CommSq (boundaryAssemblyNaturalityCylinderFamily r f)
      (boundaryAssemblyNaturalityParameterUnit r f) (terminal.from T)
      (terminal.from (boundaryAssemblyNaturalityParameters r f)) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 可縮な Kan パラメーター空間上の実際の自然性の写像族。 -/
def boundaryAssemblyNaturalityFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityParameters r f ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right :=
  Classical.choose (exists_boundaryAssemblyNaturalityFamily r f)

/-- Kan 空間への延長は二重円筒の元の族を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamily_unit (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityParameterUnit r f ≫ boundaryAssemblyNaturalityFamily r f =
      boundaryAssemblyNaturalityCylinderFamily r f :=
  Classical.choose_spec (exists_boundaryAssemblyNaturalityFamily r f)

/-- 源の構造射の全選択を自然性の Kan パラメーター空間へ含める。 -/
def boundaryAssemblyNaturalitySource (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r X ⟶ boundaryAssemblyNaturalityParameters r f :=
  boundaryAssemblyNaturalityCylinderSource r f ≫ boundaryAssemblyNaturalityParameterUnit r f

/-- 標的の構造射の全選択を自然性の Kan パラメーター空間へ含める。 -/
def boundaryAssemblyNaturalityTarget (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r Y ⟶ boundaryAssemblyNaturalityParameters r f :=
  boundaryAssemblyNaturalityCylinderTarget r f ≫ boundaryAssemblyNaturalityParameterUnit r f

/-- 自然性の族は源の元の構造射の全パラメーター族の後合成を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamily_source (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalitySource r f ≫ boundaryAssemblyNaturalityFamily r f =
      boundaryKanAssemblyAdjointFamily r X ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map f)).right := by
  rw [boundaryAssemblyNaturalitySource, Category.assoc, boundaryAssemblyNaturalityFamily_unit]
  exact boundaryAssemblyNaturalityCylinderFamily_source r f

/-- 自然性の族は標的の元の構造射の全パラメーター族の前合成を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityFamily_target (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityTarget r f ≫ boundaryAssemblyNaturalityFamily r f =
      boundaryKanAssemblyAdjointFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := by
  rw [boundaryAssemblyNaturalityTarget, Category.assoc, boundaryAssemblyNaturalityFamily_unit]
  exact boundaryAssemblyNaturalityCylinderFamily_target r f

end SerrePositivity.KST.SConstruction
