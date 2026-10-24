module

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

/-- 切断の厳密な恒等から得る可逆な単位候補。 -/
def sectionUnit (h : F ≫ G = 𝟙 X) : FunctorHom (𝟙 X) (F ≫ G) :=
  eqToHom (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f)) h.symm)

instance sectionUnit_isIso (h : F ≫ G = 𝟙 X) : IsIso (sectionUnit h) :=
  inferInstanceAs (IsIso (eqToHom _))

def adjunctionOfRelativeInitialSection (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) : QCatAdjunction F G :=
  qcatAdjunctionOfUnitMappingSpaceCondition (sectionUnit h)
    (unitCondition_of_relativeInitial (sectionUnit h) hF)

lemma adjunctionOfRelativeInitialSection_unit (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) :
    (adjunctionOfRelativeInitialSection h hF).unitHom = sectionUnit h :=
  qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ _

/-- 相対始点境界を充填する厳密切断は、全写像空間の意味で充満忠実。 -/
lemma fullyFaithful_of_relativeInitialSection (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) :
    IsFullyFaithful F := by
  have hfg : IsFullyFaithful (F ≫ G) := h.symm ▸ isFullyFaithful_id X
  intro x y
  have hg := SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary G _
    (F.app (Opposite.op ⦋0⦌) y) (hF x)
  have hc := (hfg x y).isQCatEquivalence
  rw [pinchedHomMap_comp] at hc
  exact (hg.isQCatEquivalence.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
