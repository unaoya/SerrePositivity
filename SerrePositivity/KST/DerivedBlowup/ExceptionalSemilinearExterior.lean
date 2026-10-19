module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalBasisScalarNaturality

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の半線形例外因子遷移の恒等・合成則。
方針：共通の全 a_j 表示への基底変換で共役し、自由外積の係数変更の関手性へ帰着する。
規約：ここでは総外積上の式。dg 関手の係数制限の合成比較は別に挿入する。
使われ方：実際の有限重なりの例外因子 dg 遷移の cocycle。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {I : Type} [DecidableEq I]

/-- 概要：半線形例外因子遷移の総外積上の写像。
方針：係数を変更してから、共通表示を介する可逆基底変換を施す。
規約：KST Lemma 3.6、i から k へ向く。使われ方：dg 遷移の成分の計算。 -/
def exceptionalSemilinearExteriorMap (φ : R →+* S) (x : I → R) (y : I → S) (i k : I)
    (z : ExteriorAlgebra R (I →₀ R)) : ExteriorAlgebra S (I →₀ S) :=
  ExteriorAlgebra.map (exceptionalTransitionEquiv k i y (φ ∘ x)).toLinearMap
    (freeExteriorScalarMap φ z)

/-- 概要：総外積上の半線形遷移は共通 Koszul 表示への比較と可換。
方針：行先の自己逆基底変換を消去し、始点の基底変換の係数自然性を使う。
規約：KST Lemma 3.6。使われ方：合成則を係数変更だけの合成則へ移す。 -/
theorem exceptionalSemilinearExteriorMap_comparison (φ : R →+* S)
    (x : I → R) (y : I → S) (i k : I) (z : ExteriorAlgebra R (I →₀ R)) :
    ExteriorAlgebra.map (exceptionalGeneratorMap k y)
        (exceptionalSemilinearExteriorMap φ x y i k z) =
      freeExteriorScalarMap φ (ExteriorAlgebra.map (exceptionalGeneratorMap i x) z) := by
  unfold exceptionalSemilinearExteriorMap
  have h : (exceptionalGeneratorMap k y).comp
      (exceptionalTransitionEquiv k i y (φ ∘ x)).toLinearMap =
        exceptionalGeneratorMap i (φ ∘ x) := by
    apply LinearMap.ext
    exact exceptionalTransitionEquiv_comparison k i y (φ ∘ x)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h]
  exact (freeExteriorScalarMap_natural φ (exceptionalGeneratorMap i x)
    (exceptionalGeneratorMap i (φ ∘ x)) (exceptionalGeneratorMap_scalarMap φ i x) z).symm

/-- 概要：半線形例外因子遷移の二段の合成は直接遷移と一致する。
方針：行先の可逆な共通表示比較で消去し、係数変更の合成律を使う。
規約：KST Lemma 3.6、座標の規格化を仮定せず任意の三表示を扱う。
使われ方：有限重なり環射を通る dg 遷移の合成律。 -/
theorem exceptionalSemilinearExteriorMap_comp (φ : R →+* S) (ψ : S →+* T)
    (x : I → R) (y : I → S) (z : I → T) (i k l : I)
    (m : ExteriorAlgebra R (I →₀ R)) :
    exceptionalSemilinearExteriorMap ψ y z k l (exceptionalSemilinearExteriorMap φ x y i k m) =
      exceptionalSemilinearExteriorMap (ψ.comp φ) x z i l m := by
  apply (exceptionalExteriorEquiv l z).injective
  change ExteriorAlgebra.map (exceptionalGeneratorMap l z)
      (exceptionalSemilinearExteriorMap ψ y z k l
        (exceptionalSemilinearExteriorMap φ x y i k m)) =
    ExteriorAlgebra.map (exceptionalGeneratorMap l z)
      (exceptionalSemilinearExteriorMap (ψ.comp φ) x z i l m)
  rw [exceptionalSemilinearExteriorMap_comparison, exceptionalSemilinearExteriorMap_comparison,
    exceptionalSemilinearExteriorMap_comparison, freeExteriorScalarMap_comp]

/-- 概要：恒等環射と同一表示の半線形例外因子遷移は恒等。
方針：共通表示への可逆比較を消去し、係数変更の恒等律を使う。
規約：KST Lemma 3.6。使われ方：有限重なり dg 図式の単位条件。 -/
theorem exceptionalSemilinearExteriorMap_id (x : I → R) (i : I)
    (m : ExteriorAlgebra R (I →₀ R)) :
    exceptionalSemilinearExteriorMap (RingHom.id R) x x i i m = m := by
  apply (exceptionalExteriorEquiv i x).injective
  change ExteriorAlgebra.map (exceptionalGeneratorMap i x)
      (exceptionalSemilinearExteriorMap (RingHom.id R) x x i i m) =
    ExteriorAlgebra.map (exceptionalGeneratorMap i x) m
  rw [exceptionalSemilinearExteriorMap_comparison, freeExteriorScalarMap_id]

end SerrePositivity.KST.DerivedBlowup
