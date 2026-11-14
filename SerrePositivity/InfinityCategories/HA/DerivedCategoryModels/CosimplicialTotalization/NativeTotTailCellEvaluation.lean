module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedTailFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexStrictNerveComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ全図式と同じ次数の射列を、元の閉零評価関手で評価する。 -/
def nativeTotClosedEvaluationNerve :
    nerve (CosimplicialObject (Complex A)) ⊗
      ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
        nerve (ClosedCategory A (Complex A)) where
  app _ := ↾fun p => ((p.2.down ⋙ AsSmall.down).prod' p.1) ⋙
    evaluationUncurried SimplexCategory (Complex A) ⋙ complexToClosed A
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- 同じ全閉零セル族の対角評価は元の評価関手の全射列。 -/
theorem nativeTotTailCellEvaluation_diagonal {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n)
    (d : ComposableArrows (CosimplicialObject (Complex A)) n) :
    (strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ)).app
      (Opposite.op ⦋n⦌) (d, ULift.up (𝟙 ⦋n⦌)) =
    closedNerveSimplex (((σ ⋙ AsSmall.down).prod' d) ⋙
      evaluationUncurried SimplexCategory (Complex A) ⋙ complexToClosed A) := by
  change ((strictSimplexCellFamily A (Complex A) n).orderedSimplexFamily
    (d ⋙ nativeTotTailCellFunctor A σ) (ULift.up (𝟙 ⦋n⦌))).diagonal = _
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext T a b k hT ha hb hk
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (T.isLeast_min' _).2 (T.max'_mem _)
    change compose A
      (((nativeTotTailCellFunctor A σ).map (d.map (homOfLE hab))).app b).val
      ((((nativeTotTailCellFunctor A σ).obj (d.obj a)).val.pullback (OrderHom.id)).hom
        T a b k hT ha hb hk) (add_zero k) = _
    have he := closedNerveSimplex_pullback (A := A) (D := Complex A)
      (σ ⋙ liftedClosedDiagram (d.obj a)) (OrderHom.id)
    have hh := SimplexData.data_hom_heq_of_eq
      (congrArg Simplex.toSimplexData he) T a b k hT ha hb hk
    erw [← eq_of_heq hh]
    by_cases hk0 : k = 0
    · subst hk0
      change compose A
        (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
          ((d.map (homOfLE hab)).app (AsSmall.down.obj (σ.obj b))))).val
        (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
          ((d.obj a).map (AsSmall.down.map (σ.map (homOfLE hab)))))).val _ =
        (closedHomEquiv A (Complex A) _ _ ((complexToClosed A).map
          ((((d.obj a).map (AsSmall.down.map (σ.map (homOfLE hab))))) ≫
            (d.map (homOfLE hab)).app (AsSmall.down.obj (σ.obj b))))).val
      rw [← closedHom_comp, ← (complexToClosed A).map_comp]
    · change compose A _ (closedNerveHom _ k) (add_zero k) = closedNerveHom _ k
      rw [closedNerveHom_of_ne _ _ hk0, closedNerveHom_of_ne _ _ hk0, compose_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
