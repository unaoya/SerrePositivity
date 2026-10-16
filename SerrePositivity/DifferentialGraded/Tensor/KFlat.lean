module
public import SerrePositivity.DifferentialGraded.Tensor.Yoneda
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction
public import Mathlib.Algebra.Homology.QuasiIso

/-! # A上のK-flat性とdg圏上の相対K-flat性

非有界acyclic複体を試験対象とする。相対条件はHom複体のA-flat性を仮定しない。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 任意の非有界acyclic A複体とのtensorがacyclicになる条件。 -/
def complexKFlat (K : Complex A) : Prop :=
  ∀ L : Complex A, L.Acyclic → (K ⊗ L).Acyclic

/-- A上のK-flat性は複体同型で不変。 -/
lemma complexKFlat_of_iso {K K' : Complex A} (e : K ≅ K')
    (h : complexKFlat A K') : complexKFlat A K := by
  intro L hL n
  exact (exactAt_iff_of_quasiIsoAt ((tensorRight L).mapIso e).hom n).2 (h L hL n)

/-- 複体のretractはacyclic性を保つ。 -/
lemma complex_acyclic_of_retract {K L : Complex A} (e : Retract K L) (h : L.Acyclic) :
    K.Acyclic := by
  intro n
  apply (exactAt_iff_isZero_homology K n).2
  let r := e.map (homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n)
  have hz : IsZero ((homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n).obj L) :=
    (h n).isZero_homology
  apply (Limits.IsZero.iff_id_eq_zero _).2
  calc
    𝟙 _ = r.i ≫ r.r := r.retract.symm
    _ = 0 := by rw [hz.eq_of_tgt r.i 0, zero_comp]

/-- A上のK-flat複体はretractで閉じる。 -/
lemma complexKFlat_of_retract {K K' : Complex A} (e : Retract K K')
    (h : complexKFlat A K') : complexKFlat A K := by
  intro L hL
  exact complex_acyclic_of_retract A (e.map (tensorRight L)) (h L hL)

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左dg加群のすべての評価複体がacyclicになる条件。 -/
def leftModuleAcyclic (N : LeftModule A D) : Prop :=
  ∀ x : D, (N.obj x).Acyclic

/-- 任意のobjectwise acyclic左加群をbalanced tensorで消す相対K-flat性。 -/
def moduleRelativeKFlat (M : RightModule A D) : Prop :=
  ∀ N : LeftModule A D, leftModuleAcyclic A D N → (BalancedTensor.obj A D M N).Acyclic

/-- dg圏のHomにflat性を置かず、Yoneda評価からrepresentableの相対K-flat性を得る。 -/
lemma representable_relativeKFlat (x : D) :
    moduleRelativeKFlat A D (representable A x) := by
  intro N hN n
  exact (exactAt_iff_of_quasiIsoAt (BalancedTensor.yonedaIso A D x N).hom n).2 (hN x n)

/-- 相対K-flat性は全dg自然な右加群同型で不変。 -/
lemma moduleRelativeKFlat_of_iso {M M' : RightModule A D}
    (e : ForgetEnrichment.of (Complex A) M ≅ ForgetEnrichment.of (Complex A) M')
    (h : moduleRelativeKFlat A D M') : moduleRelativeKFlat A D M := by
  intro N hN n
  exact (exactAt_iff_of_quasiIsoAt
    ((BalancedTensor.rightTensorFunctor A D N).mapIso e).hom n).2 (h N hN n)

/-- 相対K-flat右加群は全dg自然なretractで閉じる。 -/
lemma moduleRelativeKFlat_of_retract {M M' : RightModule A D}
    (e : Retract (ForgetEnrichment.of (Complex A) M) (ForgetEnrichment.of (Complex A) M'))
    (h : moduleRelativeKFlat A D M') : moduleRelativeKFlat A D M := by
  intro N hN
  exact complex_acyclic_of_retract A
    (e.map (BalancedTensor.rightTensorFunctor A D N)) (h N hN)

end SerrePositivity.DifferentialGraded
