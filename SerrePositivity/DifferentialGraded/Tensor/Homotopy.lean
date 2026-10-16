module
public import SerrePositivity.DifferentialGraded.Tensor.GradedSplitElements
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Module.Homotopy
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # balanced tensorによる全dg自然なホモトピーの保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Hom写像の閉零制限は既存balanced tensorの射になる。 -/
lemma rightHomMap_closedElement (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (rightHomMap A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) L).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom (rightTensorMap A D L f) := by
  apply cochain_zero_element_ext A D (ForgetEnrichment.to (Complex A) M) L
  intro x r s a ha m v
  rw [rightHomMap_element_of_sum A D L _ x m v ha (zero_add r) (add_zero a),
    ← moduleEvaluation_cochain A D x f]
  simp only [Cochain.ofHom_v]
  exact (rightTensorMap_element A D L f x m v ha).symm

/-- tensorの主dg関手と通常関手は閉零射で一致する。 -/
lemma rightTensorDG_map (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (closedToComplex A).map ((rightTensorDG A D L).onClosed.map f) =
      rightTensorMap A D L f := by
  apply Cochain.ofHom_injective
  have h := mapFromUnit_cochain A
    (obj A D (ForgetEnrichment.to (Complex A) M) L)
    (obj A D (ForgetEnrichment.to (Complex A) N) L)
    (ForgetEnrichment.homTo (Complex A) f ≫
      rightHomMap A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) L)
  rw [cycleFromUnit_postcomp] at h
  exact h.trans (rightHomMap_closedElement A D L f)

/-- 対象ごとの独立なホモトピーでなく、全dg自然な加群ホモトピーをtensorで送る。 -/
lemma rightTensorMap_homotopy (L : LeftModule A D) {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) :
    Nonempty (Homotopy (rightTensorMap A D L f) (rightTensorMap A D L g)) := by
  have hb := (moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩
  have ht := (rightTensorDG A D L).preserves_boundary f g hb
  have hc := (complex_boundary_iff A _ _ _ _).1 ht
  change Nonempty (Homotopy
    ((closedToComplex A).map ((rightTensorDG A D L).onClosed.map f))
    ((closedToComplex A).map ((rightTensorDG A D L).onClosed.map g))) at hc
  rw [rightTensorDG_map, rightTensorDG_map] at hc
  exact hc

/-- 固定左加群とのtensorを、主K(D)から既存K(A)への関手に降ろす。 -/
def rightTensorHomotopyFunctor (L : LeftModule A D) : ModuleHomotopyCategory A D ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _ (rightTensorFunctor A D L ⋙
    _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      obtain ⟨ht⟩ := rightTensorMap_homotopy A D L h
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ ht)

lemma rightTensorHomotopyFunctor_fac (L : LeftModule A D) :
    moduleToHomotopy A D ⋙ rightTensorHomotopyFunctor A D L =
      rightTensorFunctor A D L ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded.BalancedTensor
