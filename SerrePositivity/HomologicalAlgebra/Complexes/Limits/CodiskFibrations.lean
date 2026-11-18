module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CodiskAdjunction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DiskComponentsProjective

/-!
# 加群の全射の可縮 disk 像

概要：元の module epi の可縮 disk 像は実射影 trivial fibration。
方針：元の rank 1 disk と全 Hom 同値で各次数の全射性を検出する。
規約：誘導される同じ射自身について証明する。
使われ方：cofibrant 複体の各次数の射影性の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma codiskFunctor_map_fibration (n : ℤ) {M N : ModuleCat.{u} A} (q : M ⟶ N) [Epi q] :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A ((_root_.SerrePositivity.ComplexLimits.codiskFunctor A n).map q) := by
  intro k y
  have := _root_.SerrePositivity.ComplexLimits.complexDisk_component_projective A k n
  let b := (complexDiskHomEquiv A (_root_.SerrePositivity.ComplexLimits.codisk N n) k).symm y
  let a := _root_.SerrePositivity.ComplexLimits.codiskHomEquiv (complexDisk A k) N n b
  let g := Projective.factorThru a q
  let t := (_root_.SerrePositivity.ComplexLimits.codiskHomEquiv (complexDisk A k) M n).symm g
  have ht : t ≫ (_root_.SerrePositivity.ComplexLimits.codiskFunctor A n).map q = b := by
    apply (_root_.SerrePositivity.ComplexLimits.codiskHomEquiv (complexDisk A k) N n).injective
    rw [_root_.SerrePositivity.ComplexLimits.codiskFunctor_map_homEquiv, Equiv.apply_symm_apply]
    exact Projective.factorThru_comp a q
  refine ⟨complexDiskHomEquiv A (_root_.SerrePositivity.ComplexLimits.codisk M n) k t, ?_⟩
  calc
    _ = complexDiskHomEquiv A (_root_.SerrePositivity.ComplexLimits.codisk N n) k (t ≫ (_root_.SerrePositivity.ComplexLimits.codiskFunctor A n).map q) :=
      (complexDiskHomEquiv_naturality A k t ((_root_.SerrePositivity.ComplexLimits.codiskFunctor A n).map q)).symm
    _ = complexDiskHomEquiv A (_root_.SerrePositivity.ComplexLimits.codisk N n) k b := congrArg _ ht
    _ = y := (complexDiskHomEquiv A (_root_.SerrePositivity.ComplexLimits.codisk N n) k).apply_symm_apply y

lemma codiskFunctor_map_quasiIso (n : ℤ) {M N : ModuleCat.{u} A} (q : M ⟶ N) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.codiskFunctor A n).map q) := by
  rw [quasiIso_iff]
  intro k
  exact (quasiIsoAt_iff_exactAt _ k (_root_.SerrePositivity.ComplexLimits.codisk_acyclic M n k)).mpr (_root_.SerrePositivity.ComplexLimits.codisk_acyclic N n k)

end SerrePositivity.ComplexLimits
