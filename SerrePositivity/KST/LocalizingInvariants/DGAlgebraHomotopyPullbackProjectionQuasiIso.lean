module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso
public import SerrePositivity.KST.LocalizingInvariants.CochainKernelCoconeQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBiprodExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：右脚が準同型の実 cospan では、経路模型の元の左射影も準同型である。
方針：右脚の負符号の cocone の非輪性を、差の実 cocone 短完全列へ渡す。
規約：次数全射性や ∞ 普遍性は仮定しない。使われ方：準同型な標的模型からの実因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

lemma left_quasiIso (hg : QuasiIso g.hom) : QuasiIso (left R f g).hom := by
  have := hg
  have hneg : QuasiIso (-g.hom) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_neg]
    change IsIso (-(asIso (homologyMap g.hom j))).hom
    infer_instance
  have hz : (mappingCocone (-g.hom)).Acyclic := SerrePositivity.cochainAcyclic_shift
    ((complex_quasiIso_iff_acyclic_cone R (-g.hom)).mp hneg) (-1)
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection f.hom (-g.hom)
  have hp : QuasiIso p := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : Mono (homologyMap p j) :=
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex_shortExact f.hom (-g.hom)).homology_exact₂ j).mono_g
        ((hz j).isZero_homology.eq_of_src _ _)
    have : Epi (homologyMap p j) :=
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex_shortExact f.hom (-g.hom)).homology_exact₃ j (j + 1)
        (by change j + 1 = j + 1; rfl)).epi_f ((hz (j + 1)).isZero_homology.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  have hc : QuasiIso ((complexIso R f g).hom ≫ p) :=
    quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := hp)
  have he : (complexIso R f g).hom ≫ p = (left R f g).hom := toMappingCocone_left R f g
  exact (congrArg (fun t => QuasiIso t) he).mp hc

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
