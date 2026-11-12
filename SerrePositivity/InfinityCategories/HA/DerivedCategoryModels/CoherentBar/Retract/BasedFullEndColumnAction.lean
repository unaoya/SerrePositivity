module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndColumnAction
/-!
概要：標準単体の全ラベルの係数を始点保存ラベルへ制限し、零次数の実 Hom へ移す。
方針：部分型への線形制限と既存の全 Hom の作用を合成する。
規約：始点支持が必要な比較では支持を別に検証し、非始点保存ラベルとの自然性を主張しない。
使われ方：Hσ の普遍係数の有限面和を実境界へ移す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarBasedFullEndColumnAction {n : ℕ} (s : I _⦋n⦌) :
    (((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R) →ₗ[R]
      GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) 0 :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction R D F s).comp
    (Finsupp.lsubtypeDomain (R := R) (M := R) {a : (Δ[n] : SSet.{u}) _⦋n⦌ | a 0 = 0})

lemma dgCoherentBarBasedFullEndColumnAction_basis {n : ℕ}
    (f : ⦋n⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    dgCoherentBarBasedFullEndColumnAction R D F s
      (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F f hf s := by
  have he : (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)).subtypeDomain
      (fun a => a 0 = 0) =
      Finsupp.single
        (⟨SSet.stdSimplex.objEquiv.symm f, hf⟩ : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n) 1 := by
    classical
    change (Finsupp.single _ (1 : R)).subtypeDomain _ = _
    ext a
    simp only [Finsupp.subtypeDomain_apply, Finsupp.single_apply, Subtype.ext_iff]
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction R D F s
    ((ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)).subtypeDomain _) = _
  rw [he, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction_single]
  simp only [one_smul, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
