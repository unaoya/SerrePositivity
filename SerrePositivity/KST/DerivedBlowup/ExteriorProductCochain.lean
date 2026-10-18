module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductDegree
public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeZero

/-!
概要：KST Def3.1 の生成元追加による二成分分解を整数次数へ移す。
方針：負次数では同次外積の分解、次数0では基底環同型、正次数では零対象性を使う。
規約：q 次の項を元の複体の q+1 次と q 次の二成分へ送る。
使われ方：反復 cone 模型との項ごとの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：生成元追加後の Koszul cochain の各項を cone の二成分と同定する。
方針：負次数の外積分解を標準同型で移し、0と正次数は別に扱う。
規約：KST Def3.1、第一成分が shifted 項。
使われ方：cone 比較の componentwise isomorphism。 -/
def exteriorProductCochainEquiv (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorKoszulCochain (exteriorProductDifferential d a)).X q ≃ₗ[R]
      ((exteriorKoszulCochain d).X (q + 1) × (exteriorKoszulCochain d).X q) := by
  cases q with
  | ofNat q =>
    cases q with
    | zero =>
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d 1 (by omega))
      letI := uniqueOfSubsingleton (0 : (exteriorKoszulCochain d).X 1)
      exact ((exteriorCochainZeroIso (exteriorProductDifferential d a)).toLinearEquiv.trans
        (exteriorCochainZeroIso d).toLinearEquiv.symm).trans
          (LinearEquiv.uniqueProd (R := R) (M := (exteriorKoszulCochain d).X 0)
            (M₂ := (exteriorKoszulCochain d).X 1)).symm
    | succ n =>
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos (exteriorProductDifferential d a) (↑(n + 1)) (by omega))
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d (↑(n + 1)) (by omega))
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d (↑(n + 1) + 1) (by omega))
      exact LinearEquiv.ofSubsingleton _ _
  | negSucc n =>
    let e : (exteriorKoszulCochain d).X (Int.negSucc n + 1) ≅
        ModuleCat.of R (ExteriorAlgebra.exteriorPower R n M) :=
      (exteriorKoszulCochain d).XIsoOfEq (by omega : Int.negSucc n + 1 = -(n : ℤ)) ≪≫
        exteriorKoszulCochainXIso d n
    exact (exteriorKoszulCochainXIso (exteriorProductDifferential d a) (n + 1)).toLinearEquiv.trans
      ((exteriorProductDegreeEquiv n).trans
        (e.toLinearEquiv.symm.prodCongr (exteriorKoszulCochainXIso d (n + 1)).toLinearEquiv.symm))

end SerrePositivity.KST.DerivedBlowup
