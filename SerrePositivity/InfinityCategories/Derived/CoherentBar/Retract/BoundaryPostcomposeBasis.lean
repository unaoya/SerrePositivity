module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryCoefficientComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedEndActionPush
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.LabelBoundaryNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationBoundary_postcompose_basis {n : ℕ}
    (f : ⦋n⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) (q : ℕ) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationBoundaryGraded R D F q)
      (dgCoherentBarBasedEndColumn R D F f hf s) rfl =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (dgCoherentBarLabelBoundaryLinear R n q
        (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f))) := by
  have hpost := dgCoherentBarBasedEndColumn_postcompose R D F f hf s
    (dgCoherentBarNormalizationBoundaryGraded R D F q)
  have hcol := congrArg (fun z => compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) z
    (dgCoherentBarBasedEndBlock R D F f hf s) (show (0 : ℤ) + 0 = 0 from rfl))
    (dgCoherentBarNormalizationBoundary_coefficients R D F q ⟨n, I.map f.op s⟩)
  have hpush := dgCoherentBarBasedFullEndColumnAction_push R D F f hf s
    (dgCoherentBarUniversalBoundaryCoefficients R n q) (fun a ha =>
      dgCoherentBarUniversalBoundaryCoefficients_based R n q a (Finsupp.mem_support_iff.mp ha))
  have hnat : Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌))
      (dgCoherentBarUniversalBoundaryCoefficients R n q) =
    dgCoherentBarLabelBoundaryLinear R n q
      (ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm f)) :=
    dgCoherentBarUniversalBoundaryCoefficients_map R f q
  exact hpost.trans (hcol.trans (hpush.trans
    (congrArg (dgCoherentBarBasedFullEndColumnAction R D F s) hnat)))

end SerrePositivity.InfinityCategories
