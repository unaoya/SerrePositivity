module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellFamily
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

/-- 同じ余単体次数の射列の全図式評価を閉零セルの関手で読む。 -/
def nativeTotTailCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) n where
  obj X := ⟨closedNerveSimplex (σ ⋙ liftedClosedDiagram X)⟩
  map f := strictClosedSimplexMap (Functor.whiskerLeft σ (liftedClosedDiagramMap f))
  map_id X := by
    apply StrictSimplexMap.ext
    intro i
    exact closedHom_id _
  map_comp f g := by
    apply StrictSimplexMap.ext
    intro i
    apply Subtype.ext
    change (closedHomEquiv A (Complex A) _ _
      ((complexToClosed A).map ((f ≫ g).app (AsSmall.down.obj (σ.obj i))))).val = _
    rw [NatTrans.comp_app, (complexToClosed A).map_comp]
    exact closedHom_comp (A := A) (D := Complex A) _ _

/-- 元のweightedセルの底の面は、同じ閉零評価のHA単体。 -/
theorem nativeTotWeightedCell_tail (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    ((nativeTotWeightedCellFunctor A σ).obj X).val.pullback
        (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom = ((nativeTotTailCellFunctor A σ).obj X).val := by
  change (coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (nativeTotWeightedPrefix X σ))).pullback _ = _
  rw [← coherentSimplex_pullback]
  change coherentSimplex ((SimplicialNerve (ClosedCategory A (Complex A))).δ 0
    (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X σ))) = _
  rw [weightedConeSimplex_tail]
  have h := congrArg (fun f => f.app (Opposite.op ⦋n⦌) (σ ⋙ liftedClosedDiagram X))
    (complexClosedNerve_coherentComparison A)
  exact h

/-- 全図式射も底の面で同じ閉零評価へ戻る。 -/
theorem nativeTotWeightedCellFunctor_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom =
      nativeTotTailCellFunctor A σ := by
  apply CategoryTheory.Functor.hext
  · intro X
    exact congrArg StrictSimplexCategory.mk (nativeTotWeightedCell_tail A X σ)
  · intro X Y f
    apply StrictSimplexMap.hext
    · exact congrArg Simplex.toSimplexData (nativeTotWeightedCell_tail A X σ)
    · exact congrArg Simplex.toSimplexData (nativeTotWeightedCell_tail A Y σ)
    · intro i
      rfl

/-- 同じweightedセル族の底の面は、元の全図式評価のセル族。 -/
theorem nativeTotWeightedCellFamily_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ =
      strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ) := by
  unfold nativeTotWeightedCellFamily
  rw [← Category.assoc, ← whiskerLeft_comp, joinStdSimplexIso_leftPoint_inr]
  have hp := strictSimplexFunctorEvaluation_pullback A (Complex A)
    (nativeTotWeightedCellFunctor A σ) (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom
  rw [nativeTotWeightedCellFunctor_tail] at hp
  exact hp.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
