module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixDiagramEdge
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstTail

/-!
概要：一次 prefix の実閉零加群射を、H(G) の実辺と端点等号射で比較する。
方針：元の HA 係数の異種等号を閉零同値で戻す。
規約：元の加群射全体の等号を示し、ホモロジーだけへ弱めない。
使われ方：一次辺列のホモロジー係数の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarModuleMorphismOfCycle_transport {M N M' N' : RightModule R D}
    (hM : M = M') (hN : N = N') (f : (moduleHom R D M N).X 0)
    (hf : (moduleHom R D M N).d 0 1 f = 0)
    (g : ForgetEnrichment.of (Complex R) M' ⟶ ForgetEnrichment.of (Complex R) N')
    (hfg : HEq f (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val) :
    moduleMorphismOfCycle R D (M := ForgetEnrichment.of (Complex R) M)
      (N := ForgetEnrichment.of (Complex R) N) f hf ≫
        eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hN) =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hM) ≫ g := by
  cases hM
  cases hN
  have h := eq_of_heq hfg
  subst f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) g) = g
  exact Equiv.symm_apply_apply _ _

variable {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarSource_firstTail_nerve {n : ℕ} (s : (nerve J) _⦋n + 1⦌) :
    dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega)) =
      coherentDiagramVertex G (nerveEquiv.symm (s.obj (⟨1, by omega⟩ : Fin (n + 2)))) := by
  rw [dgCoherentBarTail_one_eq_face_zero]
  change dgCoherentBarSource R D G ⟨n, (nerve J).δ (0 : Fin (n + 2)) s⟩ = _
  rw [dgCoherentBarSource_nerve, nerve.δ_obj, Fin.succAbove_zero]
  rfl

lemma dgCoherentBarPrefixCycle_eq_diagramEdge {n : ℕ} (s : (nerve J) _⦋n + 1⦌) :
    moduleMorphismOfCycle R D
      (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨n + 1, s⟩))
      (N := ForgetEnrichment.of (Complex R)
        (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))))
      (dgCoherentBarPrefixHom R D G s 0 (by omega))
      (dgCoherentBarPrefixZeroHom_closed R D G s) ≫
        eqToHom (congrArg (ForgetEnrichment.of (Complex R))
          (dgCoherentBarSource_firstTail_nerve R D G s)) =
    eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (dgCoherentBarSource_nerve R D G (n + 1) s)) ≫
      dgCoherentBarDiagramEdge R D G (s.map (homOfLE
        (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))) :=
  dgBarModuleMorphismOfCycle_transport R D (dgCoherentBarSource_nerve R D G (n + 1) s)
    (dgCoherentBarSource_firstTail_nerve R D G s) _ _ _
      (dgCoherentBarPrefixZeroHom_heq_diagramEdge R D G s)

end SerrePositivity.InfinityCategories
