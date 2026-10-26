module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap
public import SerrePositivity.KST.NonConnective.DGKappaResolvedRelativeRoof
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
public import SerrePositivity.DifferentialGraded.Category.Restriction
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.SphereConeData

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
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve

private lemma stableClosure_map {X Y : SSet.{v}} [Quasicategory X] [IsStable X]
    [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]
    (P : Set (X _⦋0⦌)) (Q : Set (Y _⦋0⦌))
    (h : ∀ x ∈ P, F.app (Opposite.op ⦋0⦌) x ∈ Q)
    {x : X _⦋0⦌} (hx : StableVertexClosure P x) :
    StableVertexClosure Q (F.app (Opposite.op ⦋0⦌) x) := by
  induction hx with
  | of_mem hx => exact .of_mem (h _ hx)
  | of_zero hx => exact .of_zero (IsExactFunctor.preservesZero (F := F) _ hx)
  | of_iso e _ ih => exact .of_iso (VertexIso.map e F) ih
  | of_cofiber t ht _ _ ih₀ ih₁ =>
    exact .of_cofiber (t.map F (IsExactFunctor.preservesZero (F := F)))
      (IsExactFunctor.preservesCofiber (F := F) t ht) ih₀ ih₁
  | of_fiber t ht _ _ ih₁ ih₂ =>
    exact .of_fiber (t.map F (IsExactFunctor.preservesZero (F := F)))
      (IsExactFunctor.preservesFiber F t ht) ih₁ ih₂

variable (R : Type u) [CommRing R] (D E : Type (max (u + 1) v))
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (J : DGKappaConeInput R E κ)
  (M : DGKappaSuspensionMapData R D E I J)

/-- 実 resolved 射は、零化対象だけでなく同じ実安定核全体を保つ。 -/
lemma dgKappaSuspensionMap_preservesKernel :
    ∀ x, dgStableClosureProperty R _
        (resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) x →
      dgStableClosureProperty R _
        (resolvedDGNullObjects R (DGKappaCone R E J) (dgKappaConePerfectObjects R E J))
        (M.resolved.obj x) := by
  let := dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  let := dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R E J)
  let := dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGKappaCone R D I))
  let := dgNerve_isStable_of_pretriangulated R
    (DGCategoryCellResolution.Source R (DGKappaCone R E J))
  let := dgPretriangulatedFunctor_isExactFunctor R _ _ M.resolved
  intro x hx
  have h := stableClosure_map (dgNerve.map M.resolved)
    (Simplex.vertex '' resolvedDGNullObjects R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I))
    (Simplex.vertex '' resolvedDGNullObjects R (DGKappaCone R E J)
      (dgKappaConePerfectObjects R E J)) (fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨M.resolved.obj y, dgKappaSuspensionMap_preservesNullObjects R D E I J M y hy,
      (dgFunctorNerve_vertex M.resolved y).symm⟩) hx
  simpa only [dgStableClosureProperty, dgFunctorNerve_vertex] using h

/-- 同じ実小核間の厳密 dg 関手。Hom 作用は元の resolved 関手そのもの。 -/
def dgKappaSuspensionKernelFunctor :
    DGFunctor R (dgKappaResolvedKernelKInput R D I) (dgKappaResolvedKernelKInput R E J) :=
  M.resolved.restrict _ _ (dgKappaSuspensionMap_preservesKernel R D E I J M)

/-- 同じ実核包含と同じ resolved 射の四角形は厳密に可換する。 -/
lemma dgKappaSuspensionKernelFunctor_inclusion :
    (dgKappaSuspensionKernelFunctor R D E I J M).comp
        (dgKappaResolvedKernelInputMap R E J).down =
      (dgKappaResolvedKernelInputMap R D I).down.comp M.resolved :=
  M.resolved.restrict_comp_inclusion _ _ _

variable (F : DGFunctor R D E) (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 新模型の実延長の data を用いた、同じ実核間の入力射。 -/
def dgKappaSphereClosureKernelInputMap :
    dgKappaResolvedKernelKInput R D (dgKappaConeInput_unconditional' R D κ hκ) ⟶
      dgKappaResolvedKernelKInput R E (dgKappaConeInput_unconditional' R E κ hκ) :=
  ULift.up (dgKappaSuspensionKernelFunctor R D E _ _
    (dgKappaSphereClosureSuspensionMapData R D E F κ hκ))

/-- 新模型の核包含面は、同じ厳密 dg 入力射として可換する。 -/
lemma dgKappaSphereClosureKernelInputMap_inclusion :
    dgKappaSphereClosureKernelInputMap R D E F κ hκ ≫
        dgKappaResolvedKernelInputMap R E (dgKappaConeInput_unconditional' R E κ hκ) =
      dgKappaResolvedKernelInputMap R D (dgKappaConeInput_unconditional' R D κ hκ) ≫
        (ULift.up (dgKappaSphereClosureSuspensionMapData R D E F κ hκ).resolved :
          dgKappaResolvedConeKInput R D (dgKappaConeInput_unconditional' R D κ hκ) ⟶
          dgKappaResolvedConeKInput R E (dgKappaConeInput_unconditional' R E κ hκ)) := by
  apply ULift.ext
  exact dgKappaSuspensionKernelFunctor_inclusion R D E _ _ _

/-- 新模型の商射影面も、元の実商射そのもので厳密に可換する。 -/
lemma dgKappaSphereClosureSuspensionInputMap_projection :
    dgKappaResolvedSuspensionInputMap R D (dgKappaConeInput_unconditional' R D κ hκ) ≫
        dgKappaSphereClosureSuspensionInputMap R D E F κ hκ =
      (ULift.up (dgKappaSphereClosureSuspensionMapData R D E F κ hκ).resolved :
          dgKappaResolvedConeKInput R D (dgKappaConeInput_unconditional' R D κ hκ) ⟶
          dgKappaResolvedConeKInput R E (dgKappaConeInput_unconditional' R E κ hκ)) ≫
        dgKappaResolvedSuspensionInputMap R E (dgKappaConeInput_unconditional' R E κ hκ) :=
  dgKappaSuspensionInputMap_projection R D E _ _ _

/-- 同じ実核射を全対象商へ送り、固定した零角間の実入力射を得る。 -/
def dgKappaSphereClosureNullInputMap :
    dgFixedNullInput R
        (dgKappaResolvedKernelKInput R D (dgKappaConeInput_unconditional' R D κ hκ)) ⟶
      dgFixedNullInput R
        (dgKappaResolvedKernelKInput R E (dgKappaConeInput_unconditional' R E κ hκ)) :=
  ULift.up (DGQuotient.quotientDGFunctor R _ _
    (dgKappaSphereClosureKernelInputMap R D E F κ hκ).down
    Set.univ Set.univ (fun _ _ => Set.mem_univ _))

/-- 新模型の零化左面は、同じ全対象商の包含と厳密に可換する。 -/
lemma dgKappaSphereClosureNullInputMap_left :
    dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R D
        (dgKappaConeInput_unconditional' R D κ hκ)) ≫
        dgKappaSphereClosureNullInputMap R D E F κ hκ =
      dgKappaSphereClosureKernelInputMap R D E F κ hκ ≫
        dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R E
          (dgKappaConeInput_unconditional' R E κ hκ)) := by
  apply ULift.ext
  exact DGQuotient.quotientDGFunctor_inclusion R _ _ _ _ _ _

end SerrePositivity.InfinityCategories
