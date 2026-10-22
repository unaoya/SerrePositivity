module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityEvaluationReconstruction
public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealizationLarge

/-!
概要：同じ始点固定の復元射を元の大きい全空間へ移し、元の実現射との合成を照合する。
方針：小さい底変換の自然性と、元の復元射への厳密な制限公式を使う。
規約：元の全空間比較と元の c1 の実現射を保持する。
使われ方：評価変換の実際の像と持ち上げた大域評価同型の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x

/-- 同じ評価復元射の大きい全空間への像は、元の全復元射の同じ制限。 -/
lemma presheafDensityEvaluationReconstruction_largeMap :
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensityEvaluationReconstruction F x) ≫
      (smallLeftUnstraighteningIso Dx).hom ≫ leftUnstraighteningMap Dx H
        ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
        (presheafDensitySourceInclusion_source F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (twistedElementsReconstruction p) ≫
        (smallLeftUnstraighteningIso H).hom := by
  rw [← smallLeftUnstraighteningMap_naturality, ← Category.assoc, ← Functor.map_comp,
    presheafDensityEvaluationReconstruction_map, Functor.map_comp, Category.assoc]

/-- 同じ実現射の制限への合成は、元の大域評価同型の始域の同じ射。 -/
lemma presheafDensityEvaluationReconstruction_realization :
    ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensityEvaluationReconstruction F x) ≫
      (smallLeftUnstraighteningIso Dx).hom) ≫
        leftUnstraighteningMap Dx H
          ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
          (presheafDensitySourceInclusion_source F x) ≫
            coherentRealizationLargeMap H G (presheafDensityTransformation F).map =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (twistedElementsReconstruction p ≫ (presheafDensityTransformation F).map) ≫
          (smallLeftUnstraighteningIso G).hom := by
  rw [← Category.assoc, Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensityEvaluationReconstruction F x)),
    presheafDensityEvaluationReconstruction_largeMap]
  simp only [coherentRealizationLargeMap, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
