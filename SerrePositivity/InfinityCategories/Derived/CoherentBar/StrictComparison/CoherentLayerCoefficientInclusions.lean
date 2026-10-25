module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomologyInclusions
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients

/-!
概要：実次元層から非退化ホモロジー bar への同型の各係数公式。
方針：実 summand 包含の比較を、次元ラベルの再添字付けと始点同型へ送る。
規約：bar と同じ coherent 入力と実包含を使う。
使われ方：一次微分の面と辺の係数の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

@[reassoc]
lemma dgCoherentBarLayerHomologyCoefficientsIso_ι (x : D) (q : ℤ) (n : ℕ)
    (s : (nerve J).nonDegenerate n) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G n)
        (dgCoherentBarLayerIndexEquiv (nerve J) n s))) q ≫
      (dgCoherentBarLayerHomologyCoefficientsIso R D G x q n).hom =
    (dgCoherentBarLayerSummandHomologyIso R D G x q n
      (dgCoherentBarLayerIndexEquiv (nerve J) n s)).hom ≫
      (dgCoherentBarLayerCoefficientIso R D G x q n s).hom ≫
        Sigma.ι (dgHomologyBarNondegFamily R
          (dgCoherentBarHomologyDiagram R D G x ((n : ℤ) + q)) n) s := by
  let e := dgCoherentBarLayerIndexEquiv (nerve J) n
  let V := fun t : dgCoherentBarLayerIndex (nerve J) n =>
    ((dgCoherentBarSource R D G t.val.val).obj (Opposite.op x)).homology ((n : ℤ) + q)
  have hι : Sigma.ι V (e s) ≫ (Sigma.reindex e V).inv = Sigma.ι (V ∘ e) s := by
    rw [← Sigma.ι_reindex_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [dgCoherentBarLayerHomologyCoefficientsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, dgCoherentBarLayerHomologyIso_ι,
    Category.assoc]
  rw [Category.assoc, ← Category.assoc (Sigma.ι V (e s)) (Sigma.reindex e V).inv]
  erw [hι]
  rw [Sigma.ι_mapIso_hom]
  rfl

end SerrePositivity.InfinityCategories
