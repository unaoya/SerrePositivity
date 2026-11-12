module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap
public import SerrePositivity.KST.NonConnective.DGKappaResolvedRelativeRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedFunctorExact
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.SphereConeData

/-!
概要：懸垂の実射データから同じ平坦源内の実安定核への射を構成する。
方針：零化対象の保存を全安定閉包へ帰納し、元の resolved 関手を制限する。
規約：全 native 入力族や選択四角形の二胞体の自然性はここでは主張しない。
使われ方：新 sphere-only 模型の D-4b の核包含面。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.NonConnective
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open DifferentialGraded

private lemma stableClosure_map {X Y : SSet.{v}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (P : Set (X _⦋0⦌)) (Q : Set (Y _⦋0⦌))
    (h : ∀ x ∈ P, F.app (Opposite.op ⦋0⦌) x ∈ Q)
    {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure Q (F.app (Opposite.op ⦋0⦌) x) := by
  induction hx with
  | of_mem hx => exact .of_mem (h _ hx)
  | of_zero hx => exact .of_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F) _ hx)
  | of_iso e _ ih => exact .of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e F) ih
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    exact .of_cofiber (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) ih₀ ih₁
  | of_fiber t ht _ _ ih₁ ih₂ =>
    exact .of_fiber (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesFiber F t ht) ih₁ ih₂

variable (R : Type u) [CommRing R] (D E : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} D] [Small.{u} E]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (J : DGKappaConeInput R E κ)
  (M : DGKappaSuspensionMapData R D E I J)

/-- 実 resolved 射は、零化対象だけでなく同じ実安定核全体を保つ。 -/
lemma dgKappaSuspensionMap_preservesKernel :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) x →
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J))
        (M.resolved.obj x) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R E J)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R (DGKappaCone R D I))
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R (DGKappaCone R E J))
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R _ _ M.resolved
  intro x hx
  have h := stableClosure_map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map M.resolved)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R E J)
      (dgKappaConePerfectObjects R E J)) (fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨M.resolved.obj y, dgKappaSuspensionMap_preservesNullObjects R D E I J M y hy,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex M.resolved y).symm⟩) hx
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] using h

/-- 同じ実小核間の厳密 dg 関手。Hom 作用は元の resolved 関手そのもの。 -/
def dgKappaSuspensionKernelFunctor :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (dgKappaResolvedKernelKInput R D I) (dgKappaResolvedKernelKInput R E J) :=
  M.resolved.restrict _ _ (dgKappaSuspensionMap_preservesKernel R D E I J M)

/-- 同じ実核包含と同じ resolved 射の四角形は厳密に可換する。 -/
lemma dgKappaSuspensionKernelFunctor_inclusion :
    (dgKappaSuspensionKernelFunctor R D E I J M).comp
        (dgKappaResolvedKernelInputMap R E J).down =
      (dgKappaResolvedKernelInputMap R D I).down.comp M.resolved :=
  M.resolved.restrict_comp_inclusion _ _ _

variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 新模型の実延長の data を用いた、同じ実核間の入力射。 -/
def dgKappaSphereClosureKernelInputMap :
    dgKappaResolvedKernelKInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) ⟶
      dgKappaResolvedKernelKInput R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ) :=
  ULift.up (dgKappaSuspensionKernelFunctor R D E _ _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionMapData R D E F κ hκ))

/-- 新模型の核包含面は、同じ厳密 dg 入力射として可換する。 -/
lemma dgKappaSphereClosureKernelInputMap_inclusion :
    dgKappaSphereClosureKernelInputMap R D E F κ hκ ≫
        dgKappaResolvedKernelInputMap R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ) =
      dgKappaResolvedKernelInputMap R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) ≫
        (ULift.up (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionMapData R D E F κ hκ).resolved :
          dgKappaResolvedConeKInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) ⟶
          dgKappaResolvedConeKInput R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ)) := by
  apply ULift.ext
  exact dgKappaSuspensionKernelFunctor_inclusion R D E _ _ _

/-- 新模型の商射影面も、元の実商射そのもので厳密に可換する。 -/
lemma dgKappaSphereClosureSuspensionInputMap_projection :
    dgKappaResolvedSuspensionInputMap R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R D E F κ hκ =
      (ULift.up (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionMapData R D E F κ hκ).resolved :
          dgKappaResolvedConeKInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) ⟶
          dgKappaResolvedConeKInput R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ)) ≫
        dgKappaResolvedSuspensionInputMap R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ) :=
  dgKappaSuspensionInputMap_projection R D E _ _ _

/-- 同じ実核射を全対象商へ送り、固定した零角間の実入力射を得る。 -/
def dgKappaSphereClosureNullInputMap :
    dgFixedNullInput R
        (dgKappaResolvedKernelKInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)) ⟶
      dgFixedNullInput R
        (dgKappaResolvedKernelKInput R E (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ)) :=
  ULift.up (_root_.SerrePositivity.DifferentialGraded.DGQuotient.quotientDGFunctor R _ _
    (dgKappaSphereClosureKernelInputMap R D E F κ hκ).down
    Set.univ Set.univ (fun _ _ => Set.mem_univ _))

/-- 新模型の零化左面は、同じ全対象商の包含と厳密に可換する。 -/
lemma dgKappaSphereClosureNullInputMap_left :
    dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R D
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)) ≫
        dgKappaSphereClosureNullInputMap R D E F κ hκ =
      dgKappaSphereClosureKernelInputMap R D E F κ hκ ≫
        dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R E
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R E κ hκ)) := by
  apply ULift.ext
  exact _root_.SerrePositivity.DifferentialGraded.DGQuotient.quotientDGFunctor_inclusion R _ _ _ _ _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
