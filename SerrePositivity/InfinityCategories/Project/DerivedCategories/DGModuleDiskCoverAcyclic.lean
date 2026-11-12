module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexShortExactQuasiIso
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import Mathlib.Algebra.Category.ModuleCat.AB
/-!
概要：実 disk 被覆の非有界非輪状性と、非輪状直和項からの射影の準同型性。
方針：自由 disk の実余積・exact な余極限・同じ split 短完全列を使う。
規約：平坦性やモデル圏を仮定しない。使われ方：任意の準同型の実全射 span。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の全次数 disk 被覆は、全評価で非有界に非輪状。 -/
lemma dgModuleDiskCover_acyclic (M : ModuleCategory R D) :
    moduleAcyclic R D (moduleDiskCover R D M) := by
  intro x i
  let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex R D M)) (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex R D M)).symm)
  exact (complex_colimit_acyclic R
    (Discrete.functor (moduleDiskCoverFamily R D M) ⋙ moduleEvaluation R D x)
    (fun j => freeDisk_acyclic R D j.as.1 j.as.2.1 x) i).of_iso
      (preservesColimitIso (moduleEvaluation R D x)
        (Discrete.functor (moduleDiskCoverFamily R D M))).symm
/-- 非輪状な第二直和項からの同じ第一射影は準同型。 -/
lemma complexBiprod_fst_quasiIso_of_acyclic (X K : Complex R) (hK : K.Acyclic) :
    QuasiIso (biprod.fst : X ⊞ K ⟶ X) := by
  let S : ShortComplex (Complex R) := ShortComplex.mk
    (biprod.inr : K ⟶ X ⊞ K) (biprod.fst : X ⊞ K ⟶ X) (by simp)
  have hS : S.Splitting :=
    { r := biprod.snd
      s := biprod.inl
      f_r := by simp [S]
      s_g := by simp [S]
      id := by dsimp [S]; rw [add_comm, biprod.total] }
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexShortExact_quasiIso_projection S hS.shortExact hK
/-- 非輪状な第二加群直和項からの同じ第一射影は全評価で準同型。 -/
lemma dgModuleBiprodFst_quasiIso_of_acyclic (M K : ModuleCategory R D)
    (hK : moduleAcyclic R D K) : moduleQuasiIso R D (moduleBiprodFst R D M K) := by
  intro x
  rw [moduleBiprodFst_eval]
  exact complexBiprod_fst_quasiIso_of_acyclic R ((moduleEvaluation R D x).obj M)
    ((moduleEvaluation R D x).obj K) (hK x)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
