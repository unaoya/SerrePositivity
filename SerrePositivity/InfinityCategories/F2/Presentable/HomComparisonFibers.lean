module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparison
public import SerrePositivity.InfinityCategories.F1.CosliceFiberDiagramChange
public import SerrePositivity.InfinityCategories.F1.PullbackFiber
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection

/-!
概要：元の coslice 比較の各 fiber を、同じ関手の元の写像空間比較へ戻す。
方針：厳密な引き戻しの fiber 同型で同じ後合成作用を回収し、F1 の模型比較を使う。
規約：元の比較射・始点・終点を保持。全対象の同値性は仮定しない。
使われ方：Ind 比較の全 Hom 比較の成分を判定するための実 fiber 側の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

attribute [local instance] vertexFiber_kanComplex_of_leftFibration
local instance {C D : SSet.{u}} [Quasicategory D] (G : C ⟶ D) (x : C _⦋0⦌) :
    LeftFibration (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)))⟩

/-- 比較の実 fiber は、引き戻し同型の後で元の coslice の後合成そのもの。 -/
lemma cosliceComparisonOver_fiber_postcomp {C D : SSet.{u}}
    (G : C ⟶ D) (x y : C _⦋0⦌) :
    vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G)
      (cosliceComparisonOver G x) (cosliceComparisonOver_projection G x) y ≫
        (vertexFiberPullbackIso (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G y).hom =
          coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) G y := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc,
    vertexFiberMap_ι, Category.assoc, cosliceComparisonOver_postcomp,
    coslicePostcompFiberMap_ι]

/-- 元の比較の指定 fiber の同値性は、元の指定二対象間の pinchedHomMap の同値性。 -/
lemma cosliceComparisonOver_fiber_equivalence_iff {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (G : C ⟶ D) (x y : C _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G)
      (cosliceComparisonOver G x) (cosliceComparisonOver_projection G x) y) ↔
        IsSimplicialHomotopyEquivalence (pinchedHomMap G x y) := by
  have he : IsQCatEquivalence
      (vertexFiberPullbackIso (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G y).hom :=
    QCatEquivalence.isQCatEquivalence (qCatEquivalenceOfIso
      (vertexFiberPullbackIso (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G y))
  have h : IsQCatEquivalence (vertexFiberMap
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G)
      (cosliceComparisonOver G x) (cosliceComparisonOver_projection G x) y) ↔
      IsQCatEquivalence (coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) G y) := by
    constructor
    · intro h
      rw [← cosliceComparisonOver_fiber_postcomp]
      exact h.comp he
    · intro h
      apply he.cancel_right
      rw [cosliceComparisonOver_fiber_postcomp]
      exact h
  have hm := pointCosliceFiberMap_equivalence_iff_pinchedHomMap G x y
  rw [pointCosliceFiberMap_eq_postcomp] at hm
  have hd : IsQCatEquivalence
      (cosliceFiberDiagramIso (SSet.yonedaEquiv_symm_comp x G)
        (G.app (Opposite.op ⦋0⦌) y)).hom :=
    (qCatEquivalenceOfIso (cosliceFiberDiagramIso (SSet.yonedaEquiv_symm_comp x G)
      (G.app (Opposite.op ⦋0⦌) y))).isQCatEquivalence
  exact h.trans ⟨fun hc ↦ hm.mp (hc.comp hd), fun hc ↦ hd.cancel_right (hm.mpr hc)⟩

/-- 固定始点の全写像空間比較は、元の底上の coslice 比較の前合成同値性と同値。 -/
lemma cosliceComparisonOver_precompositionEquivalence_iff {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (G : C ⟶ D) (x : C _⦋0⦌) :
    IsPrecompositionEquivalence (cosliceComparisonOver G x) ↔
      ∀ y : C _⦋0⦌, IsSimplicialHomotopyEquivalence (pinchedHomMap G x y) := by
  rw [leftFibration_precompositionEquivalence_iff_fibers
    (sliceUnderProjection (SSet.yonedaEquiv.symm x))
    (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G)
    (cosliceComparisonOver G x) (cosliceComparisonOver_projection G x)]
  exact forall_congr' (cosliceComparisonOver_fiber_equivalence_iff G x)

/-- 全充満忠実性は、全始点の同じ coslice 比較の前合成同値性で検出される。 -/
lemma isFullyFaithful_iff_cosliceComparisonOver {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (G : C ⟶ D) :
    IsFullyFaithful G ↔ ∀ x : C _⦋0⦌, IsPrecompositionEquivalence (cosliceComparisonOver G x) := by
  exact (forall_congr' (cosliceComparisonOver_precompositionEquivalence_iff G)).symm

end SerrePositivity.InfinityCategories.F2.Presentable
