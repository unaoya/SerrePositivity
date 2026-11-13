module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedRelativeRoof
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableClosureFullyFaithful
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
概要：同じ平坦分解の実小核を、元の cone 内の perfect 安定閉包へ照合する。
方針：元の増大の全写像空間の同値と完全性で実安定閉包の所属を保存・反映する。
規約：同じ K-B 核に特殊化する。一般商 API を追加せず、Perf・P 全関手照合の完成とは数えない。
使われ方：K-7 c5 の D-9 実核と、P が指定する元の安定閉包との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ増大による生成頂点の像は、元の cone の同じ perfect 対象の頂点集合そのもの。 -/
theorem dgKappaResolvedKernel_generators_image :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))).app
      (Opposite.op ⦋0⦌) ''
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I)
          (dgKappaConePerfectObjects R D I)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' dgKappaConePerfectObjects R D I := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x, hx,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    let x : DGCategoryCellResolution.Source R (DGKappaCone R D I) := ⟨y⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ⟨x, hy, rfl⟩, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    rfl

/-- 実小核の所属は、同じ増大後の元の perfect 安定閉包の所属と同値。 -/
theorem dgKappaResolvedKernel_membership_iff
    (x : DGCategoryCellResolution.Source R (DGKappaCone R D I)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
        ((DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x) ↔
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGCategoryCellResolution.Source R (DGKappaCone R D I))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) x := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGKappaCone R D I))
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentationNerve_isQCatEquivalence R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence he
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)))
    he.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  rw [dgKappaResolvedKernel_generators_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at h
  exact h

/-- 元の同じ増大を、実小核から元の perfect 安定閉包へ全 Hom ごと制限する。 -/
def dgKappaResolvedKernelAugmentation : DGFunctor R (dgKappaResolvedKernelKInput R D I)
    (DGFullSubcategory (DGKappaCone R D I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))) :=
  (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).restrict _ _
    (fun x hx => (dgKappaResolvedKernel_membership_iff R D I x).mpr hx)

/-- 元の包含と制限増大の合成は、同じ実核包含と元の増大の合成に全 Hom 上で一致する。 -/
theorem dgKappaResolvedKernelAugmentation_inclusion :
    (dgKappaResolvedKernelAugmentation R D I).comp
      (dgFullSubcategoryInclusion R (DGKappaCone R D I)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))) =
      (dgKappaResolvedKernelInputMap R D I).down.comp
        (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) :=
  DGFunctor.restrict_comp_inclusion _ _ _ _

/-- 同じ実核から元の安定閉包への増大は、各 Hom 複体で準同型。 -/
theorem dgKappaResolvedKernelAugmentation_homQuasiIso :
    HomQuasiIso (dgKappaResolvedKernelAugmentation R D I) := by
  intro x y
  exact DGCategoryCellResolution.augmentation_homQuasiIso R (DGKappaCone R D I) x.val y.val

/-- 同じ実核から元の安定閉包への制限増大は準同値。対象ラベルを変えない。 -/
theorem dgKappaResolvedKernelAugmentation_quasiEquivalence :
    QuasiEquivalence (dgKappaResolvedKernelAugmentation R D I) := by
  refine ⟨dgKappaResolvedKernelAugmentation_homQuasiIso R D I, ?_⟩
  constructor
  intro Y
  let N := ForgetEnrichment.to (Complex R) Y.as
  let x : DGCategoryCellResolution.Source R (DGKappaCone R D I) := ⟨N.val⟩
  let M : dgKappaResolvedKernelKInput R D I :=
    ⟨x, (dgKappaResolvedKernel_membership_iff R D I x).mp N.property⟩
  exact ⟨(toHomotopy R (dgKappaResolvedKernelKInput R D I)).obj
    (ForgetEnrichment.of (Complex R) M), ⟨Iso.refl _⟩⟩

/-- 同じ実小核の native nerve と P が指定する元の安定閉包との全写像空間の同値。 -/
def dgKappaResolvedKernelNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgQuasiEquivalenceNerveEquivalence (dgKappaResolvedKernelAugmentation R D I)
    (dgKappaResolvedKernelAugmentation_quasiEquivalence R D I)

/-- 元の二つの実包含は、同じ増大を通すと全単体上で厳密に一致する。 -/
theorem dgKappaResolvedKernelAugmentation_nerve_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelAugmentation R D I) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelInputMap R D I).down ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgKappaResolvedKernelAugmentation_inclusion]

end SerrePositivity.KST.NonConnective
