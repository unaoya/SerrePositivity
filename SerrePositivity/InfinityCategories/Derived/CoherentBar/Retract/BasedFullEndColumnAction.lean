module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedEndColumnAction
/-!
概要：標準単体の全ラベルの係数を始点保存ラベルへ制限し、零次数の実 Hom へ移す。
方針：部分型への線形制限と既存の全 Hom の作用を合成する。
規約：始点支持が必要な比較では支持を別に検証し、非始点保存ラベルとの自然性を主張しない。
使われ方：Hσ の普遍係数の有限面和を実境界へ移す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarBasedFullEndColumnAction {n : ℕ} (s : I _⦋n⦌) :
    (((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R) →ₗ[R]
      GradedHom R (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0 :=
  (dgCoherentBarBasedEndColumnAction R D F s).comp
    (Finsupp.lsubtypeDomain (R := R) (M := R) {a : (Δ[n] : SSet.{u}) _⦋n⦌ | a 0 = 0})

lemma dgCoherentBarBasedFullEndColumnAction_basis {n : ℕ}
    (f : ⦋n⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    dgCoherentBarBasedFullEndColumnAction R D F s
      (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)) =
      dgCoherentBarBasedEndColumn R D F f hf s := by
  have he : (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)).subtypeDomain
      (fun a => a 0 = 0) =
      Finsupp.single
        (⟨SSet.stdSimplex.objEquiv.symm f, hf⟩ : DGCoherentBarBasedLabel.{u} n n) 1 := by
    classical
    change (Finsupp.single _ (1 : R)).subtypeDomain _ = _
    ext a
    simp only [Finsupp.subtypeDomain_apply, Finsupp.single_apply, Subtype.ext_iff]
  change dgCoherentBarBasedEndColumnAction R D F s
    ((ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)).subtypeDomain _) = _
  rw [he, dgCoherentBarBasedEndColumnAction_single]
  simp only [one_smul, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
