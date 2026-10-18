module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalBasis

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の基底変換を重なりに接続する。
方針：各 pivot の関係式を共通の全 a_j の列へ移し、その比較を共役して遷移を作る。
規約：同一重なり係数環上の段階。環射による係数移送と dg 降下は別段階。
使われ方：例外因子の Ko(A;a)[S] 表示をチャート間で整合させる。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：共通の全 a_j 表示を介する例外因子の生成加群の遷移。
方針：始点の基底変換に行先の基底変換の逆を続ける。
規約：KST Lemma 3.6、k から i の向き。使われ方：重なりと cocycle。 -/
def exceptionalTransitionEquiv (i k : I) (x y : I → B) : (I →₀ B) ≃ₗ[B] (I →₀ B) :=
  (exceptionalGeneratorEquiv k y).trans (exceptionalGeneratorEquiv i x).symm

/-- 概要：例外因子の遷移の具体的な二段の線形写像。
方針：各基底変換の自己逆性を定義から読む。
規約：KST Lemma 3.6。使われ方：微分とチャート遷移との比較。 -/
theorem exceptionalTransitionEquiv_apply (i k : I) (x y : I → B) (z : I →₀ B) :
    exceptionalTransitionEquiv i k x y z =
      exceptionalGeneratorMap i x (exceptionalGeneratorMap k y z) := rfl

/-- 概要：共通表示への基底変換は例外因子の遷移と可換。
方針：行先の自己逆基底変換を二度適用して消去する。
規約：KST Lemma 3.6。使われ方：Ko(A;a)[S] の局所比較の整合性。 -/
theorem exceptionalTransitionEquiv_comparison (i k : I) (x y : I → B) (z : I →₀ B) :
    exceptionalGeneratorMap i x (exceptionalTransitionEquiv i k x y z) =
      exceptionalGeneratorMap k y z := by
  rw [exceptionalTransitionEquiv_apply]
  exact LinearMap.congr_fun (exceptionalGeneratorMap_comp i x) _

/-- 概要：例外因子の遷移は関係式による微分を保つ。
方針：両方の関係式を同じ全 a_j の線形形式へ移す。
規約：KST Lemma 3.6、正則性や座標の規格化は不要。
使われ方：外積 Koszul 複体上の遷移を定義する微分条件。 -/
theorem exceptionalTransitionEquiv_differential (a x y : I → B) (i k : I) :
    (Finsupp.linearCombination B (exceptionalRelationValue a x i)).comp
        (exceptionalTransitionEquiv i k x y).toLinearMap =
      Finsupp.linearCombination B (exceptionalRelationValue a y k) := by
  apply LinearMap.ext
  intro z
  calc
    _ = Finsupp.linearCombination B a
        (exceptionalGeneratorMap i x (exceptionalTransitionEquiv i k x y z)) :=
      (LinearMap.congr_fun (exceptionalGeneratorMap_differential a x i) _).symm
    _ = Finsupp.linearCombination B a (exceptionalGeneratorMap k y z) := by
      rw [exceptionalTransitionEquiv_comparison]
    _ = _ := LinearMap.congr_fun (exceptionalGeneratorMap_differential a y k) z

/-- 概要：例外因子の遷移は三重重なりで cocycle を満たす。
方針：中間 pivot の自己逆基底変換を消去する。
規約：KST Lemma 3.6、三つの表示を同じ係数環に移した形。
使われ方：全有限重なりの例外因子図式への接続。 -/
theorem exceptionalTransitionEquiv_cocycle (i k l : I) (x y z : I → B) :
    (exceptionalTransitionEquiv k l y z).trans (exceptionalTransitionEquiv i k x y) =
      exceptionalTransitionEquiv i l x z := by
  apply LinearEquiv.ext
  intro m
  change exceptionalGeneratorMap i x
    (exceptionalGeneratorMap k y (exceptionalGeneratorMap k y (exceptionalGeneratorMap l z m))) =
      exceptionalGeneratorMap i x (exceptionalGeneratorMap l z m)
  exact congrArg (exceptionalGeneratorMap i x)
    (LinearMap.congr_fun (exceptionalGeneratorMap_comp k y) _)

/-- 概要：同一表示の例外因子の遷移は恒等。
方針：自己逆基底変換の二段を消去する。
規約：KST Lemma 3.6。使われ方：有限重なり図式の単位条件。 -/
theorem exceptionalTransitionEquiv_id (i : I) (x : I → B) :
    exceptionalTransitionEquiv i i x x = LinearEquiv.refl B (I →₀ B) := by
  apply LinearEquiv.ext
  intro z
  exact LinearMap.congr_fun (exceptionalGeneratorMap_comp i x) z

end SerrePositivity.KST.DerivedBlowup
