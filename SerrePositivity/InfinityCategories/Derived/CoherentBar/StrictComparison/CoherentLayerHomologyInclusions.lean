module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomology

/-!
概要：実次元層のホモロジー同型に対する summand 包含の公式。
方針：直和比較の自然性と各整数 shift のホモロジー同型を合わせる。
規約：同じ coherent 入力の実包含を使う。
使われ方：実一次ホモロジー微分の各係数の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

@[reassoc]
lemma dgCoherentBarLayerHomologyIso_ι (x : D) (q : ℤ) (n : ℕ)
    (s : dgCoherentBarLayerIndex I n) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G n) s)) q ≫
        (dgCoherentBarLayerHomologyIso R D G x q n).hom =
    (dgCoherentBarLayerSummandHomologyIso R D G x q n s).hom ≫
      Sigma.ι (fun t : dgCoherentBarLayerIndex I n =>
        ((dgCoherentBarSource R D G t.val.val).obj
          (Opposite.op x)).homology ((n : ℤ) + q)) s := by
  have h : (dgCoherentBarLayerHomologyIso R D G x q n).hom =
      (dgModuleCoproductHomologyIso R D (dgCoherentBarLayerFamily R D G n) x q).hom ≫
        (Sigma.mapIso (dgCoherentBarLayerSummandHomologyIso R D G x q n)).hom := by
    simp only [dgCoherentBarLayerHomologyIso, dgModuleCoproductHomologyIso,
      Iso.trans_hom, Category.assoc]
  rw [h, ← Category.assoc, dgModuleCoproductHomologyIso_ι]
  exact Sigma.ι_mapIso_hom _ s

end SerrePositivity.InfinityCategories
