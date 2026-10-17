module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseExtensions
public import SerrePositivity.DifferentialGraded.Module.TensorUnit
public import SerrePositivity.DifferentialGraded.Module.FreeSphereShift
public import SerrePositivity.DifferentialGraded.Module.ResolutionSequence
public import SerrePositivity.DifferentialGraded.Complexes.ExactColimits
public import SerrePositivity.DifferentialGraded.Derived.AcyclicZero
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # 標準解像度の有限高さの段階への有限 cell 因子分解

各段の cell の個数は有限と仮定しない。既存の実際の cone と射影余積を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleFiniteCellOver_freeSphere {S : Set D} (x : D) (hx : x ∈ S) (n : ℤ) :
    moduleFiniteCellOver A D S (freeSphere A D x n) := by
  have h0 : moduleFiniteCellOver A D S (freeSphere A D x 0) :=
    moduleFiniteCellOver_of_iso A D (moduleTensorUnitIso A D (representable A x)).symm
      (moduleFiniteCellOver_representable A D x hx)
  exact moduleFiniteCellOver_of_iso A D
    (freeSphereShiftIso A D x 0 (-n) ≪≫ eqToIso
      (congrArg (freeSphere A D x) (by omega : 0 - -n = n)))
    (moduleFiniteCellOver_shift A D h0 (-n))

lemma moduleFiniteCellFactorTarget_coproduct_small {S : Set D} {J : Type w} [Small.{u} J]
    (F : J → DerivedModuleCategory A D) (hF : ∀ j, moduleFiniteCellFactorTarget A D S (F j)) :
    moduleFiniteCellFactorTarget A D S (∐ F) := by
  let e : Shrink.{u} J ≃ J := (equivShrink J).symm
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso (Sigma.reindex e F)
    (moduleFiniteCellFactorTarget_coproduct A D (F ∘ e) (fun j => hF (e j)))

lemma moduleFiniteCellFactorTarget_projectiveCoproduct {S : Set D} {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (hF : ∀ j, moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (M j))) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj (∐ M)) := by
  let hc := colimit.isColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (M j)))
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (hc.coconePointUniqueUpToIso (moduleProjectiveDerivedCofanIsColimit A D M hM))
    (moduleFiniteCellFactorTarget_coproduct_small A D _ hF)

lemma moduleFiniteCellFactorTarget_sphereCoproduct {J : Type w} [Small.{u} J]
    (x : J → D) (n : J → ℤ) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (∐ fun j => freeSphere A D (x j) (n j))) :=
  moduleFiniteCellFactorTarget_projectiveCoproduct A D _
    (fun j => freeSphere_homotopicallyProjective A D (x j) (n j))
    (fun j => moduleFiniteCellFactorTarget_of_finiteCell A D
      ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCellOver_freeSphere A D (x j) (Set.mem_univ _) (n j))))

lemma moduleFiniteCellFactorTarget_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) := by
  induction n with
  | zero =>
    apply (moduleFiniteCellFactorTarget A D Set.univ).prop_of_isZero
    apply moduleToDerived_isZero_of_acyclic A D
    intro x i
    let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex A D M)) (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
        (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex A D M)).symm)
    exact (complex_colimit_acyclic A
      (Discrete.functor (moduleDiskCoverFamily A D M) ⋙ moduleEvaluation A D x)
      (fun j => freeDisk_acyclic A D j.as.1 j.as.2.1 x) i).of_iso
        (preservesColimitIso (moduleEvaluation A D x)
          (Discrete.functor (moduleDiskCoverFamily A D M))).symm
  | succ n ih =>
    exact (moduleFiniteCellFactorTarget A D Set.univ).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D
        (moduleKernelCellMap A D (moduleResolutionStage A D M n).hom))
      (moduleFiniteCellFactorTarget_sphereCoproduct A D _ _) ih

end SerrePositivity.DifferentialGraded
