module
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TrivialFibrationCofinality
/-!
概要：全値が始対象である実図式から指定対象への全三角形は、元の添字と弱ホモトピー同値。
方針：各 fiber を同じ出る pinched Hom と同定し、可縮 fiber の右ファイブレーション判定を使う。
規約：添字の quasicategory 性は不要。使われ方：実逆分母に付随する商側三角形の弱可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
/-- 全値が始対象の実図式への指定終点 slice の引き戻しは、元の添字へ自明 Kan に射影する。 -/
lemma initialDiagramSliceProjection_trivialKanFibration {I E : SSet.{u}} [Quasicategory E]
    (a : I ⟶ E) (ha : ∀ i, IsInitialVertex (a.app (Opposite.op ⦋0⦌) i)) (b : E _⦋0⦌) :
    TrivialKanFibration (pullback.fst a (sliceOverProjection (SSet.yonedaEquiv.symm b))) := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm b)
  have h : TrivialKanFibration (pullback.snd p a) := by
    apply rightFibration_trivialKanFibration_of_contractible_fibers
    intro i
    apply vertexFiber_pullback_isContractibleKan
    exact (qCatEquivalenceOfIso (pinchedHomSliceFiberIso _ b)).isContractibleKan
      (F1B.kanInitialVertex_pinchedHom_isContractibleKan (ha i) b)
  have : TrivialKanFibration (pullback.snd p a) := h
  let e := pullbackSymmetry a p
  have : TrivialKanFibration e.hom := inferInstance
  have hc : TrivialKanFibration (e.hom ≫ pullback.snd p a) :=
    ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem TrivialKanFibration.mem⟩
  dsimp only [e] at hc
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc
/-- 弱可縮な添字上の始対象値図式から指定対象への全実三角形は弱可縮。 -/
lemma initialDiagramSlice_isWeaklyContractible {I E : SSet.{u}} [Quasicategory E]
    (a : I ⟶ E) (ha : ∀ i, IsInitialVertex (a.app (Opposite.op ⦋0⦌) i)) (b : E _⦋0⦌)
    (hI : IsWeaklyContractible I) :
    IsWeaklyContractible (pullback a (sliceOverProjection (SSet.yonedaEquiv.symm b))) := by
  have := initialDiagramSliceProjection_trivialKanFibration a ha b
  have hw := (isLeftCofinal_of_trivialKanFibration
    (pullback.fst a (sliceOverProjection (SSet.yonedaEquiv.symm b)))).isWeakHomotopyEquivalence
  exact hw.weaklyContractible_iff.mpr hI
end SerrePositivity.InfinityCategories
