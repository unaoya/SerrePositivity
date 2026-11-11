module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryCoefficientComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndActionPush
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryNaturality
/-!
概要：実境界を始点保存の基底列へ合成すると、Hσ をその基底へ作用させた係数列になる。
方針：境界の列比較、始点支持つき係数押出し、Mathlib の自然性を順に接続する。
規約：全段階と全自己写像について同じ零次数 Hom の等式を与える。
使われ方：有限係数和への線形延長を通じた実正規化段階の帰納比較。
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

lemma dgCoherentBarNormalizationBoundary_postcompose_basis {n : ℕ}
    (f : ⦋n⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) (q : ℕ) :
    _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F f hf s) rfl =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q
        (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f))) := by
  have hpost := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn_postcompose R D F f hf s
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q)
  have hcol := congrArg (fun z => _root_.SerrePositivity.DifferentialGraded.compose R
    (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) z
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndBlock R D F f hf s) (show (0 : ℤ) + 0 = 0 from rfl))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationBoundary_coefficients R D F q ⟨n, I.map f.op s⟩)
  have hpush := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction_push R D F f hf s
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients R n q) (fun a ha =>
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_based R n q a (Finsupp.mem_support_iff.mp ha))
  have hnat : Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients R n q) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarLabelBoundaryLinear R n q
      (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)) :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_map R f q
  exact hpost.trans (hcol.trans (hpush.trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedFullEndColumnAction R D F s) hnat)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
