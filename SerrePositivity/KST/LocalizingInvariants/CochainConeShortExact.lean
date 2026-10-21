module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
概要：実 cone の包含・shift 射影は、次数ごとに分裂する短完全列をなす。
方針：元の二射影・二包含と shift の符号を保持して分裂を構成する。
規約：射影は標準 cone 三角形の境界。使われ方：Postnikov cone の実 pullback 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {M K : Complex R} (i : M ⟶ K)

def cochainConeSequence : ShortComplex (Complex R) :=
  ShortComplex.mk (mappingCone.inr i) (mappingCone.triangle i).mor₃
    (mappingCone.inr_triangleδ i)

def cochainConeSequence_splitting (n : ℤ) :
    ((cochainConeSequence i).map (HomologicalComplex.eval _ _ n)).Splitting := by
  let e := M.shiftFunctorObjXIso 1 n (n + 1) (by omega)
  let t := (mappingCone.inl i).v (n + 1) n (by omega)
  exact {
    r := (mappingCone.snd i).v n n (add_zero n)
    s := -(e.hom ≫ t)
    f_r := by simp [cochainConeSequence]
    s_g := by
      dsimp [cochainConeSequence, t]
      simp [e]
      rfl
    id := by
      dsimp [cochainConeSequence]
      apply mappingCone.ext_from i (n + 1) n rfl
      · simp [t, e]
      · simp [t, e] }

lemma cochainConeSequence_shortExact : (cochainConeSequence i).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (cochainConeSequence_splitting i n).shortExact

lemma cochainConeInr_mono : Mono (mappingCone.inr i) :=
  (cochainConeSequence_shortExact i).mono_f

def cochainConeInr_isKernel : IsLimit
    (KernelFork.ofι (mappingCone.inr i) (mappingCone.inr_triangleδ i)) := by
  have : Mono (cochainConeSequence i).f := (cochainConeSequence_shortExact i).mono_f
  exact (cochainConeSequence_shortExact i).exact.fIsKernel

end SerrePositivity.KST.LocalizingInvariants
