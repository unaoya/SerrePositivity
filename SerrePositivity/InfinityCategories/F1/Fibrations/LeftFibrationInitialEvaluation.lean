module

public import SerrePositivity.InfinityCategories.F1B.KanInitialSectionLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Fibrations.AllEdges
public import SerrePositivity.InfinityCategories.Stable.IdentityCocone

/-!
概要：left fibration の相対関手空間の始対象での評価は、自明 Kan fibration。
方針：全ての辺が cocartesian であることにより切断の全部分複体を元の相対 Hom と同定する。
規約：任意の底上の図式と、任意の高次・境界固定パラメーターを保つ。
使われ方：coslice の恒等錐の点から、全対象の coherent な比較を同時に構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories

/-- left fibration 上では、cocartesian 切断の包含は相対 Hom 空間全体との同型。 -/
lemma kanCocartesianSectionsι_isIso_of_leftFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) : IsIso (kanCocartesianSectionsι p a) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    exact Subtype.ext h
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro i e
    exact isCocartesianEdge_of_leftFibration p _

/-- 始対象での実際の相対 Hom の評価は、全境界を固定した持ち上げを持つ。 -/
lemma relativeFunctorEvaluate_initial_trivialKanFibration {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (v : A _⦋0⦌) (hv : IsInitialVertex v) :
    TrivialKanFibration (relativeFunctorEvaluate p a v) := by
  have := kanCocartesianSectionsι_isIso_of_leftFibration p a
  have ht := kanCocartesianSectionsEvaluate_trivialKanFibration p a v hv
  have he : relativeFunctorEvaluate p a v =
      (asIso (kanCocartesianSectionsι p a)).inv ≫ kanCocartesianSectionsEvaluate p a v := by
    exact ((asIso (kanCocartesianSectionsι p a)).inv_hom_id_assoc
      (relativeFunctorEvaluate p a v)).symm
  rw [he]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (MorphismProperty.rlp_of_isIso _ _) ht.mem⟩

/-- coslice 上の実際の相対 Hom の恒等錐での評価は、自明 Kan fibration。 -/
lemma leftFibration_cosliceIdentityEvaluation_trivialKanFibration
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    TrivialKanFibration (relativeFunctorEvaluate p
      (sliceUnderProjection (SSet.yonedaEquiv.symm b)) (cosliceIdentityCone b)) :=
  relativeFunctorEvaluate_initial_trivialKanFibration p _ _ (cosliceIdentityCone_isInitialVertex b)

end SerrePositivity.InfinityCategories
