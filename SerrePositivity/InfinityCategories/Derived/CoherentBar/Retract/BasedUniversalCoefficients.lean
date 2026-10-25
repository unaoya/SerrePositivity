module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoefficientAction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.UniversalLabelNaturality
/-!
概要：普遍正規化係数を始点保存ラベルの部分型へ制限しても、退化による押し出しは零である。
方針：始点支持で制限を戻し、ラベル全体での退化消滅を単射性により反映する。
規約：始点を変えるラベルを零作用として扱わず、支持された係数だけを使う。
使われ方：実加群の始点保存作用に普遍係数の退化消滅を適用する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]

def dgCoherentBarBasedUniversalCoefficients (n : ℕ) : DGCoherentBarBasedLabel.{u} n n →₀ R :=
  (dgCoherentBarUniversalCoefficients R n).subtypeDomain (fun a => a 0 = 0)

lemma dgCoherentBarBasedUniversalCoefficients_extend (n : ℕ) :
    Finsupp.mapDomain Subtype.val (dgCoherentBarBasedUniversalCoefficients R n) =
      dgCoherentBarUniversalCoefficients R n := by
  calc
    _ = Finsupp.embDomain (Function.Embedding.subtype (fun a : (Δ[n] : SSet.{u}) _⦋n⦌ => a 0 = 0))
        (dgCoherentBarBasedUniversalCoefficients R n) :=
      (Finsupp.embDomain_eq_mapDomain _ _).symm
    _ = (dgCoherentBarBasedUniversalCoefficients R n).extendDomain :=
      (Finsupp.extendDomain_eq_embDomain_subtype _).symm
    _ = _ := Finsupp.extendDomain_subtypeDomain _ (fun a ha =>
      dgCoherentBarUniversalCoefficients_based R n a (Finsupp.mem_support_iff.mp ha))

lemma dgCoherentBarBasedUniversalCoefficients_degeneracy (n : ℕ) (j : Fin (n + 1)) :
    Finsupp.mapDomain (dgCoherentBarBasedLabelPush (SimplexCategory.σ j) (by
      change j.predAbove 0 = 0
      simp)) (dgCoherentBarBasedUniversalCoefficients R (n + 1)) = 0 := by
  apply Finsupp.mapDomain_injective (f := Subtype.val) Subtype.val_injective
  rw [Finsupp.mapDomain_zero, ← Finsupp.mapDomain_comp]
  change Finsupp.mapDomain
    (((SSet.stdSimplex.map (SimplexCategory.σ j)).app (Opposite.op ⦋n + 1⦌)) ∘ Subtype.val)
    (dgCoherentBarBasedUniversalCoefficients R (n + 1)) = 0
  rw [Finsupp.mapDomain_comp, dgCoherentBarBasedUniversalCoefficients_extend]
  exact dgCoherentBarUniversalCoefficients_degeneracy R n j

variable (D : Type v) [DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶
    dgNerve R (DifferentialGraded.RightModule R D))

lemma dgCoherentBarBasedUniversalAction_degeneracy (n : ℕ) (j : Fin (n + 1)) :
    dgCoherentBarBasedMap R D F (SimplexCategory.σ j) (by
      change j.predAbove 0 = 0
      simp) ≫ dgCoherentBarBasedCoefficientAction R D F (n + 1) (n + 1)
        (dgCoherentBarBasedUniversalCoefficients R (n + 1)) = 0 := by
  rw [dgCoherentBarBasedCoefficientAction_push,
    dgCoherentBarBasedUniversalCoefficients_degeneracy, map_zero]

end SerrePositivity.InfinityCategories
