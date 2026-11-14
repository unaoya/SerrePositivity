module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeCellEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedNerveCoefficientProjection

/-!
概要：元のnative Tot錐の全cosliceセルは、同じprefix入力のweightedセルそのもの。
方針：任意次数の切断評価と、パラメータ第一射影の元の係数則を合成。
規約：IS-W2 D01の既存構成の表示・貼り合わせ則。同じ全セルを厳密等式で保つ。
使われ方：HA 1.2.4、元のnative錐からStrictCoherentFamilyへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 任意次数の元のnative Tot錐の切断セルを、同じweighted simplexで読む。 -/
theorem nativeTotCone_cosliceCell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    (((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ))).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ)) := by
  rw [nativeTotCone_cosliceSection_simplex X σ a₀]
  change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
    (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (weightedNerveCoefficients
        (fst (bousfieldKanWeight (AsSmall.{u} SimplexCategory))
          ((Functor.const (AsSmall.{u} SimplexCategory)).obj (Δ[0] : SSet.{u})) ≫
            liftedEnrichedBousfieldKanCone X) σ (SSet.yonedaEquiv.symm a₀))) = _
  rw [weightedNerveCoefficients_fst]
  all_goals rfl

/-- 元のnative Tot錐の同じ全join射を、同じweightedセル上で制限する。 -/
theorem nativeTotCone_cellMap (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ)) :=
  (coherentConeCosliceSection_cell (nativeCoherentCone X) _
    (nativeCoherentCone_vertex X) (ULift.up σ)).symm.trans
      (nativeTotCone_cosliceCell X σ a₀)

/-- 同じ標準セルで読む元のnative Tot錐の単体は、同じweighted simplex。 -/
theorem nativeTotCone_cellSimplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val) =
      weightedConeSimplex (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (nativeTotWeightedPrefix X σ) := by
  rw [nativeTotCone_cellMap X σ a₀, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
