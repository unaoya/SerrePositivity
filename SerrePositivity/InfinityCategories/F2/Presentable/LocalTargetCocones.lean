module

public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalSectionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport

/-!
概要：終点が局所対象である元の coherent な余錐の圏。
方針：元の coslice 射影を局所対象の全部分圏へ引き戻す。
規約：図式の添字は任意。使われ方：局所置換の普遍矢印性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X : SSet.{u}} [Quasicategory X]

/-- 元の図式の余錐のうち、可変な終点が指定辺集合に対して局所であるもの。 -/
def localTargetCoconeSpace (W : Set (X _⦋1⦌)) {K : SSet.{u}} (D : K ⟶ X) : SSet.{u} :=
  pullback (sliceUnderProjection D) (localObjectsSubcomplex W).ι

/-- 元の局所対象への終点射影。 -/
def localTargetCoconeProjection (W : Set (X _⦋1⦌)) {K : SSet.{u}} (D : K ⟶ X) :
    localTargetCoconeSpace W D ⟶ (localObjectsSubcomplex W : SSet.{u}) :=
  pullback.snd _ _

/-- 局所終点の余錐の射影も left fibration。 -/
instance localTargetCoconeProjection_leftFibration (W : Set (X _⦋1⦌))
    {K : SSet.{u}} (D : K ⟶ X) : LeftFibration (localTargetCoconeProjection W D) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := sliceUnderProjection D))⟩

/-- 局所終点の余錐全体は quasicategory。 -/
instance localTargetCoconeSpace_quasicategory (W : Set (X _⦋1⦌))
    {K : SSet.{u}} (D : K ⟶ X) : Quasicategory (localTargetCoconeSpace W D) :=
  quasicategory_of_innerFibration (localTargetCoconeProjection W D)

/-- 部分図式への余錐制限は、元の局所終点を保持する。 -/
def localTargetCoconeRestriction (W : Set (X _⦋1⦌)) {J K : SSet.{u}}
    (D : J ⟶ X) (d : K ⟶ X) (i : K ⟶ J) (hi : i ≫ D = d) :
    localTargetCoconeSpace W D ⟶ localTargetCoconeSpace W d :=
  SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange (sliceUnderProjection D) (sliceUnderProjection d)
    (normalizedCoconeRestriction D i hi) (normalizedCoconeRestriction_projection D i hi)
    (localObjectsSubcomplex W).ι

/-- 局所終点の制限を忘れると、元の余錐制限を回収。 -/
lemma localTargetCoconeRestriction_fst (W : Set (X _⦋1⦌)) {J K : SSet.{u}}
    (D : J ⟶ X) (d : K ⟶ X) (i : K ⟶ J) (hi : i ≫ D = d) :
    localTargetCoconeRestriction W D d i hi ≫
      pullback.fst (sliceUnderProjection d) (localObjectsSubcomplex W).ι =
    pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι ≫
      normalizedCoconeRestriction D i hi :=
  pullback.lift_fst _ _ _

/-- 局所終点を固定した余錐制限は、元の各局所対象上で同値なら全体でも同値。 -/
lemma localTargetCoconeRestriction_isQCatEquivalence (W : Set (X _⦋1⦌))
    {J K : SSet.{u}} (D : J ⟶ X) (d : K ⟶ X) (i : K ⟶ J) (hi : i ≫ D = d)
    (h : ∀ z : X _⦋0⦌, IsLocalObject W z →
      IsQCatEquivalence (normalizedCoconeRestrictionFiber D i hi z)) :
    IsQCatEquivalence (localTargetCoconeRestriction W D d i hi) := by
  apply F1B.kanIsQCatEquivalence_of_leftFibration_fibers
    (localTargetCoconeProjection W D) (localTargetCoconeProjection W d) _
    (SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_projection _ _ _ _ _)
  intro z
  apply (qCatEquivalenceOfIso (cofinalVertexFiberBaseChangeIso (sliceUnderProjection d)
    (localObjectsSubcomplex W).ι z)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (_ ≫ (cofinalVertexFiberBaseChangeIso (sliceUnderProjection d)
    (localObjectsSubcomplex W).ι z).hom)
  dsimp only [localTargetCoconeProjection, localTargetCoconeSpace]
  rw [SerrePositivity.InfinityCategories.F1B.fiberComparisonBaseChange_fiber]
  exact (qCatEquivalenceOfIso (cofinalVertexFiberBaseChangeIso (sliceUnderProjection D)
    (localObjectsSubcomplex W).ι z)).isQCatEquivalence.comp
      (h z.val (fullSubcomplexOnVertices_vertex z))

/-- 指定辺の始点への局所終点の余錐制限は同値。 -/
lemma localTargetCoconeRestriction_source_isQCatEquivalence (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ localEquivalences W) :
    IsQCatEquivalence (localTargetCoconeRestriction W e (stdSimplex.δ (1 : Fin 2) ≫ e)
      (stdSimplex.δ (1 : Fin 2)) rfl) := by
  apply localTargetCoconeRestriction_isQCatEquivalence
  intro z hz
  have := sourceRestriction_trivial_of_localObject (localEquivalences W) e he
    ((isLocalObject_localEquivalences_iff W z).mpr hz)
  simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
    (isQCatEquivalence_of_trivialKanFibration
      (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) z))

/-- 辺の終点への局所終点の余錐制限は常に同値。 -/
lemma localTargetCoconeRestriction_target_isQCatEquivalence (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    IsQCatEquivalence (localTargetCoconeRestriction W e (stdSimplex.δ (0 : Fin 2) ≫ e)
      (stdSimplex.δ (0 : Fin 2)) rfl) := by
  apply localTargetCoconeRestriction_isQCatEquivalence
  intro z _
  have := cosliceTriangleTarget_trivialKanFibration e z
  simpa only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using
    (isQCatEquivalence_of_trivialKanFibration
      (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) z))

end SerrePositivity.InfinityCategories.HomotopyLimits
