module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeInitialAdjunction

public import SerrePositivity.KST.LocalizingInvariants.PinchedPrecomposeEquivalence
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitMappingAdjunction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：相対始点境界を充填する切断は、元の射影の左随伴になる。
方針：相対充填で得る元の写像空間の同値に、可逆な指定単位で前合成する。
規約：随伴や写像空間の同値性を追加仮定にしない。使われ方：K-8 の D 包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

lemma unitCondition_of_relativeInitial (η : FunctorHom (𝟙 X) (F ≫ G)) [IsIso η]
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) :
    UnitMappingSpaceCondition η := by
  intro x y
  rw [unitPinchedMap_formula]
  have : IsIso (qcatUnitComponent η x) := by
    change IsIso (functorHomEvaluate η x)
    infer_instance
  exact ((SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary G _ y (hF x)).isQCatEquivalence.comp
    (PinchedPrecompose.isQCatEquivalence (qcatUnitComponent η x) _)).isSimplicialHomotopyEquivalence

def adjunctionOfRelativeInitialSection (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) : QCatAdjunction F G :=
  qcatAdjunctionOfUnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit h)
    (unitCondition_of_relativeInitial (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit h) hF)

lemma adjunctionOfRelativeInitialSection_unit (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) :
    (adjunctionOfRelativeInitialSection h hF).unitHom = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit h :=
  qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ _

end SerrePositivity.KST.LocalizingInvariants
