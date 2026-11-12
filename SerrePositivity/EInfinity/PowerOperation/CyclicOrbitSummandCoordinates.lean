module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitFiniteCoordinates
public import SerrePositivity.EInfinity.PowerOperation.FiniteBiproductCoordinates

/-!
# orbit の指定包含射を有限座標へ移す

DAG XIII Construction 2.2.6 の鎖模型比較の補助。
元の直和全複体の指定成分を、同じ正則評価と双積の指定包含で記述する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]
variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)

/-- 同じ有限対角線の包含射の、指定座標での式。 -/
lemma cyclicOrbitTotalDegreeCoordinates_inclusion
    (s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)}) :
    ιMapBifunctor M (cyclicOrbitResolution p k)
        (Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)) (.up ℤ)
        (s.1 + n) (-s.1) n (by change s.1 + n + -s.1 = n; omega) ≫
      (cyclicOrbitTotalDegreeCoordinatesIso p k M d n).hom =
    (cyclicOrbitFiniteSummandIso p k M d n s).hom ≫
      biproduct.ι (fun s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)} =>
        ModuleCat.of k (M.X (s.1 + n))) s ≫
      (ModuleCat.biproductIsoPi _).hom := by
  classical
  let q := ((cyclicOrbitFiniteDiagonalEquiv d n).symm s)
  have h := coproductZeroSupportIso_inclusion
    (cyclicOrbitDiagonalSummand p k M n)
    (fun q => q.1.2 ≤ 0 ∧ q.1.1 ≤ d)
    (cyclicOrbitDiagonalSummand_isZero p k M d n) q
  change Sigma.ι (fun q : {q : CyclicOrbitDiagonal n // q.1.2 ≤ 0 ∧ q.1.1 ≤ d} =>
    cyclicOrbitDiagonalSummand p k M n q.1) q ≫
    (cyclicOrbitTotalDegreeSupportIso p k M d n).hom =
    Sigma.ι (cyclicOrbitDiagonalSummand p k M n) q.1 at h
  have h' := congrArg (fun f => f ≫ (cyclicOrbitTotalDegreeSupportIso p k M d n).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  dsimp only [cyclicOrbitTotalDegreeCoordinatesIso, cyclicOrbitTotalDegreeFiniteSumIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change Sigma.ι (cyclicOrbitDiagonalSummand p k M n) q.1 ≫ _ = _
  erw [← Category.assoc, ← h']
  dsimp only [q]
  erw [Sigma.ι_reindex_inv_assoc]
  erw [Sigma.ι_mapIso_hom_assoc]
  simp only [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc]

/-- 元の指定成分の包含射を、各有限座標で評価した Kronecker の式。 -/
lemma cyclicOrbitTotalDegreeCoordinates_inclusion_apply
    (s t : {s : ℤ // s ∈ Finset.Icc 0 (d - n)})
    (x : cyclicOrbitDiagonalSummand p k M n
      ((cyclicOrbitFiniteDiagonalEquiv d n).symm s).1) :
    (cyclicOrbitTotalDegreeCoordinatesIso p k M d n).hom.hom
      ((ιMapBifunctor M (cyclicOrbitResolution p k)
        (Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)) (.up ℤ)
        (s.1 + n) (-s.1) n (by change s.1 + n + -s.1 = n; omega)).hom x) t =
    if h : s = t then
      (eqToHom (congrArg (fun s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)} =>
        ModuleCat.of k (M.X (s.1 + n))) h)).hom
          ((cyclicOrbitFiniteSummandIso p k M d n s).hom.hom x)
    else 0 := by
  let F : {s : ℤ // s ∈ Finset.Icc 0 (d - n)} → ModuleCat.{u} k :=
    fun s => ModuleCat.of k (M.X (s.1 + n))
  have h := congrArg (fun f => f.hom x)
    (cyclicOrbitTotalDegreeCoordinates_inclusion p k M d n s)
  have h' := congrArg (fun v => v t) h
  change (cyclicOrbitTotalDegreeCoordinatesIso p k M d n).hom.hom _ t =
    (ModuleCat.biproductIsoPi F).hom.hom
      ((biproduct.ι F s).hom ((cyclicOrbitFiniteSummandIso p k M d n s).hom.hom x)) t at h'
  exact h'.trans (finiteBiproductCoordinates_inclusion F s t
    ((cyclicOrbitFiniteSummandIso p k M d n s).hom.hom x))

end SerrePositivity.EInfinity.PowerOperation
