module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryPostcomposeBasis
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PostcompositionLinear
/-!
概要：実境界を始点支持のある任意の係数列へ合成すると、Hσ の係数作用に一致する。
方針：二つの R 線形写像を単項基底で比較し、支持による部分型からの延長を使う。
規約：始点支持を明示し、閉射やホモトピー類だけの比較に弱めない。
使われ方：P の係数再帰を実正規化段階へ帰納する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationBoundary_postcompose_based_coefficients {n : ℕ}
    (s : I _⦋n⦌) (q : ℕ) (z : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n →₀ R) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction R D F s z) rfl =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q (Finsupp.mapDomain Subtype.val z)) := by
  let L := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractPostcompositionLinear R D
    (M := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (N := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (P := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (p := 0) (q := 0) (k := 0)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q) rfl).comp
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction R D F s)
  let G := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s).comp
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q).comp
      (Finsupp.lmapDomain R R
        (Subtype.val : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n → (Δ[n] : SSet.{u}) _⦋n⦌)))
  have hlinear : L = G := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction R D F s (Finsupp.single a 1)) rfl =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q
          (Finsupp.mapDomain Subtype.val (Finsupp.single a 1)))
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumnAction_single, one_smul, Finsupp.mapDomain_single]
    simpa only [Equiv.symm_apply_apply, ModuleCat.freeMk] using
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationBoundary_postcompose_basis R D F
        (SSet.stdSimplex.objEquiv a.val) a.property s q
  exact LinearMap.congr_fun hlinear z

lemma dgCoherentBarNormalizationBoundary_postcompose_coefficients {n : ℕ}
    (s : I _⦋n⦌) (q : ℕ) (z : ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R)
    (hz : ∀ a ∈ z.support, a 0 = 0) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s z) rfl =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q z) := by
  have h := dgCoherentBarNormalizationBoundary_postcompose_based_coefficients R D F s q
    (z.subtypeDomain (fun a => a 0 = 0))
  exact h.trans (congrArg (fun v => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q v)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedCoefficients_extend R z hz))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
