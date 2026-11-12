module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeEvaluation
public import SerrePositivity.KST.SConstruction.DGNativePointLeft
/-!
概要：全 native dg 関手族を元対象に固定した評価を厳密回収する。
方針：元 tensor の第二包含と同じ豊穣単位を使う。
規約：標的 Small 仮定なし。全高次単体を保持する。
使われ方：全 cone 四角形の対象別押し出し性の照合。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
universe u
/-- 概要：元対象に固定した tensor 評価は同じ end 評価関手。
方針：元単位挿入を全 Hom 成分で照合する。
規約：全 Hom の厳密等号。使われ方：対象別の元二単体の回収。 -/
lemma dgFunctorTensorEvaluation_atPoint (R : Type u) [CommRing R] (D E : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R E] (x : D) :
    (dgTensorIncludeSecond R D (DGFunctor R D E) x).comp
      (dgFunctorTensorEvaluation R D E) = dgFunctorEvaluationDG R D E x := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro F G
  apply (Category.comp_id _).trans
  change dgTensorSecondHom R D (DGFunctor R D E) x F G ≫
    dgFunctorTensorEvalHom R D E (x, F) (x, G) = dgFunctorHomπ R D E F G x
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (dgFunctorTensorEvalHom R D E (x, F) (x, G)).f p
    ((dgTensorSecondHom R D (DGFunctor R D E) x F G).f p a) =
    (dgFunctorHomπ R D E F G x).f p a
  rw [dgTensorSecondHom_apply]
  have hv := dgFunctorTensorEvalHom_element R D E
    (x := ((x, F) : DGTensorCategory R D (DGFunctor R D E)))
    (y := ((x, G) : DGTensorCategory R D (DGFunctor R D E)))
    (unitElement R x).val a (zero_add p)
  apply hv.trans
  rw [DGFunctor.map_unitElement]
  simpa only [compose, zero_mul, Int.negOnePow_zero, one_smul] using
    compose_unit R ((dgFunctorHomπ R D E F G x).f p a)

/-- 概要：同じ固定対象で native 全単体を評価すると元評価の像そのもの。
方針：左点 tensor の全作用素則と厳密 dg 評価回収を使う。
規約：全単体次数での厳密等号。使われ方：元全 cone 図式の点評価。 -/
lemma dgFunctorNativeEvaluation_atPoint (R : Type u) [CommRing R] (D E : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R E] (x : D)
    {N : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R D E) N) :
    (dgNerveTensorSimplex R (dgNativePointSimplex R D x N) t).map
      (dgFunctorTensorEvaluation R D E) = t.map (dgFunctorEvaluationDG R D E x) := by
  have ht := dgNerveTensorSimplex_point_left R x t
  apply (congrArg (fun s => s.map (dgFunctorTensorEvaluation R D E)) ht).trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (t.toSimplexData.map _).map _ = t.toSimplexData.map _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, dgFunctorTensorEvaluation_atPoint]

/-- 概要：元 native 全関手族の点評価は同じ dg end 評価の nerve 像。
方針：元単位頂点での curry 評価と全単体の固定対象則を合成する。
規約：全単体の厳密等号。使われ方：元 cone 全族の点ごとの普遍性。 -/
lemma dgFunctorNativeFullFamilyMap_atPoint (R : Type u) [CommRing R] (D E : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R E] (x : D) :
    dgFunctorNativeFullFamilyMap R D E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFunctorEvaluationDG R D E x) := by
  let v : 𝟙_ SSet.{u + 1} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D :=
    (unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  have hv : unitHomEquiv _ v = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x :=
    (unitHomEquiv _).apply_symm_apply _
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv (dgFunctorNativeEvaluation R D E) v
  have hvn (n : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u + 1}).obj n) :
      v.app n a = dgNativePointSimplex R D x n.unop.len := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x).pullback
      (SimplexCategory.const n.unop ⦋0⦌ 0).toOrderHom = _
    rw [← dgNativePointSimplex_zero R D x]
    exact dgNativePointSimplex_pullback R D x _
  change curry (dgFunctorNativeEvaluation R D E) ≫ _ = _
  rw [← hv, h]
  ext n t
  change (dgNerveTensorSimplex R (v.app n PUnit.unit) t).map
    (dgFunctorTensorEvaluation R D E) = t.map (dgFunctorEvaluationDG R D E x)
  exact (congrArg (fun s => (dgNerveTensorSimplex R s t).map
    (dgFunctorTensorEvaluation R D E)) (hvn n PUnit.unit)).trans
      (dgFunctorNativeEvaluation_atPoint R D E x t)

end SerrePositivity.KST.SConstruction
