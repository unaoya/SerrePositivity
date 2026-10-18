module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductCochain
public import SerrePositivity.KST.DerivedBlowup.ExteriorInclusionTransport

/-!
概要：KST Def3.1 の整数次数の二成分分解を総外積上で評価する。
方針：負次数は同次分解、次数0は係数同型、正次数は零対象性で比較する。
規約：第一成分は収縮後の射影、第二成分は射影。
使われ方：cone 微分との chain 条件の証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：整数次数の二成分分解の第二成分は外積の射影。
方針：標準同型と包含を比較する。
規約：KST Def3.1。使われ方：cone の非 shifted 成分の微分比較。 -/
theorem exteriorProductCochainEquiv_snd (d : M →ₗ[R] R) (a : R) (q : ℤ)
    (z : (exteriorKoszulCochain (exteriorProductDifferential d a)).X q) :
    exteriorCochainInclusion d q (exteriorProductCochainEquiv d a q z).2 =
      exteriorProductOut (exteriorCochainInclusion (exteriorProductDifferential d a) q z) := by
  cases q with
  | ofNat q =>
    cases q with
    | zero =>
      change exteriorCochainInclusion d 0
        ((exteriorCochainZeroIso d).inv
          ((exteriorCochainZeroIso (exteriorProductDifferential d a)).hom z)) =
        exteriorProductOut (exteriorCochainInclusion (exteriorProductDifferential d a) 0 z)
      rw [exteriorCochainInclusion_zero_inv, exteriorCochainInclusion_zero]
      exact (AlgHom.commutes _ _).symm
    | succ n =>
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos (exteriorProductDifferential d a) (↑(n + 1)) (by omega))
      have hz : z = 0 := Subsingleton.elim _ _
      rw [hz, map_zero]
      change exteriorCochainInclusion d _ 0 = exteriorProductOut (exteriorCochainInclusion _ _ 0)
      rw [map_zero, map_zero, map_zero]
  | negSucc n =>
    change exteriorCochainInclusion d (-((n + 1 : ℕ) : ℤ))
      ((exteriorKoszulCochainXIso d (n + 1)).inv
        (exteriorDegreeMap (LinearMap.fst R M R) (n + 1)
          ((exteriorKoszulCochainXIso (exteriorProductDifferential d a) (n + 1)).hom z))) = _
    rw [exteriorCochainInclusion_standard_inv]
    rfl

/-- 概要：整数次数の二成分分解の第一成分は最後の座標での収縮成分。
方針：標準同型と添字等式による移送を比較する。
規約：KST Def3.1。使われ方：cone の shifted 成分の微分比較。 -/
theorem exteriorProductCochainEquiv_fst (d : M →ₗ[R] R) (a : R) (q : ℤ)
    (z : (exteriorKoszulCochain (exteriorProductDifferential d a)).X q) :
    exteriorCochainInclusion d (q + 1) (exteriorProductCochainEquiv d a q z).1 =
      exteriorProductTail (exteriorCochainInclusion (exteriorProductDifferential d a) q z) := by
  cases q with
  | ofNat q =>
    cases q with
    | zero =>
      change 0 = exteriorProductOut
        (CliffordAlgebra.contractLeft (Q := 0) (LinearMap.snd R M R)
          (exteriorCochainInclusion (exteriorProductDifferential d a) 0 z))
      rw [exteriorContraction_zero_degree _ _ (exteriorCochainInclusion_mem _ 0 z), map_zero]
    | succ n =>
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos (exteriorProductDifferential d a) (↑(n + 1)) (by omega))
      have hz : z = 0 := Subsingleton.elim _ _
      rw [hz, map_zero]
      change exteriorCochainInclusion d _ 0 = exteriorProductTail (exteriorCochainInclusion _ _ 0)
      rw [map_zero, map_zero, map_zero]
  | negSucc n =>
    let hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    change exteriorCochainInclusion d (Int.negSucc n + 1)
      (((exteriorKoszulCochain d).XIsoOfEq hn).inv
        ((exteriorKoszulCochainXIso d n).inv
          (exteriorProductDegreeTail n
            ((exteriorKoszulCochainXIso (exteriorProductDifferential d a) (n + 1)).hom z)))) = _
    rw [exteriorCochainInclusion_XIsoOfEq_inv, exteriorCochainInclusion_standard_inv]
    rfl

end SerrePositivity.KST.DerivedBlowup
