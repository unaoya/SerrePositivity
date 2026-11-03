-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoid.FiniteProduct（仮。2a の Perfectoidization* の統合先に合わせる。completed-tensor-split.md §2・§3）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md G-A6-12、completed-tensor-split.md §3。基準コミット 1ed122760。ビルドしない。
-- BS-W10 作業 A で `CompletedTensor.lean` の `isIntegralPerfectoid_finPi`（E3 を使う旧証明）をこの直接証明に差し替える。
module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# perfectoid 環の有限直積は perfectoid（G-A6-12、E3 非依存の直接証明）

## 概要
R・S が perfectoid（`IsIntegralPerfectoid`）なら R × S も perfectoid。帰納で `Fin r → R`（r = 0 は零環）と、添字 ι が有限な `∀ i, A i` も。
既存の `isIntegralPerfectoid_finPi`（CompletedTensor.lean）は E3 の `Inputs.exists_perfectoidization_of_integral` を使うので、E3 を消す組み立てでは使えない（W9-III-08）。

## 方針
成分ごとの判定：p 進完備性・p = aϖ^p・mod p の Frobenius 全射は成分ごと。Fontaine 核の単項性は、ModP・Perfection（PreTilt）・Witt ベクトルが
有限直積と可換であること（係数ごとの計算）と θ の両立から、ker θ_{R×S} = ker θ_R × ker θ_S = ((ξ_R, ξ_S))。
`isIntegralPerfectoid_of_compatible_p_roots`（Perfectoid/Fontaine.lean）は p 正則を仮定するので一般には使わない。

## 規約
零環を含める（`IsIntegralPerfectoid` の左の選択肢）。`Fact (¬IsUnit (p : R × S))` と `IsAdicComplete` の直積のインスタンスは補題で供給し、定理の中で `letI`。

## 使われ方
A6 §2.2（R → ∏R_i への置き換え、`PerfdSmall` の有限積）、G-A6-2、CLMST の `isIntegralPerfectoid_finPi` の利用側（名前を保つ）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.BhattScholze

open WittVector

variable (p : ℕ) [Fact p.Prime]

/-! ## 直積の基本的な両立 -/

section Prod
variable (R S : Type u) [CommRing R] [CommRing S]

/-- 概要：どちらかの因子で p が単元でなければ直積でも単元でない。
方針：単元の射影。
規約：—
使われ方：`Fact (¬IsUnit (p : R × S))` の供給。 -/
theorem not_isUnit_p_prod_left (h : ¬ IsUnit (p : R)) : ¬ IsUnit (p : R × S) := by
  sorry -- 射影 R × S → R は単元を単元に送る

/-- 概要：p 進完備性は有限直積で保たれる（`IsHausdorff`・`IsPrecomplete` を成分ごとに）。
方針：Mathlib に直積版が見当たらないので成分ごとの合同で書く（`Ideal.span {(p : R × S)}` の冪は成分ごとの冪の直積）。
規約：—
使われ方：直積の `IsAdicComplete`。 -/
theorem isAdicComplete_span_p_prod [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : R × S)}) (R × S) := by
  sorry -- 成分ごと

/-- 概要：(R × S)/p ≅ R/p × S/p。
方針：`Ideal.quotientInfEquivQuotientProd` 系か、射影の対の全射性と核の計算。
規約：`ModP O p := O ⧸ span {p}`（Mathlib）。
使われ方：Frobenius の全射性、PreTilt の直積。 -/
def modPProdEquiv : ModP (R × S) p ≃+* ModP R p × ModP S p := sorry

/-- 概要：Frobenius の全射性は有限直積で保たれる。
方針：`modPProdEquiv` と成分ごと。
規約：—
使われ方：`isIntegralPerfectoid_prod`。 -/
theorem surjective_pow_p_modP_prod
    (hR : Function.Surjective (fun x : ModP R p ↦ x ^ p)) (hS : Function.Surjective (fun x : ModP S p ↦ x ^ p)) :
    Function.Surjective (fun x : ModP (R × S) p ↦ x ^ p) := by
  sorry

/-- 概要：Perfection は有限直積と可換（Frobenius に沿う逆極限は有限積と可換。係数 `Perfection.coeff` ごとに）。
方針：`Perfection.map` の射影の対で射を作り、係数で単射・全射。
規約：A・B は標数 p。
使われ方：PreTilt の直積。 -/
def perfectionProdEquiv (A B : Type u) [CommRing A] [CommRing B] [CharP A p] [CharP B p] :
    Perfection (A × B) p ≃+* Perfection A p × Perfection B p := sorry

/-- 概要：Witt ベクトルは有限直積と可換：W(A × B) ≅ W(A) × W(B)。
方針：`WittVector.map` の射影の対（環準同型）。逆は係数ごとに `(a_n, b_n)` を置く。`map_coeff` で両立。
規約：Mathlib に直積の同型はないので係数で書く。
使われ方：θ の直積。 -/
def wittVectorProdEquiv (A B : Type u) [CommRing A] [CommRing B] :
    WittVector p (A × B) ≃+* WittVector p A × WittVector p B :=
  RingEquiv.ofBijective ((WittVector.map (RingHom.fst A B)).prod (WittVector.map (RingHom.snd A B))) (by
    sorry) -- Witt の各係数の対を逆写像にする

end Prod

/-! ## Fontaine 核の直積 -/

section Theta
variable (R S : Type u) [CommRing R] [CommRing S]
variable [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 概要：PreTilt(R × S) ≅ PreTilt R × PreTilt S。
方針：`modPProdEquiv` と `perfectionProdEquiv`（ModP の標数 p は Mathlib のインスタンス）。
規約：`PreTilt O p := Perfection (ModP O p) p`。
使われ方：θ の直積。 -/
def preTiltProdEquiv :
    letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
    PreTilt (R × S) p ≃+* PreTilt R p × PreTilt S p := by
  letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
  let l := Perfection.map p (modPMap p (RingHom.fst R S))
  let r := Perfection.map p (modPMap p (RingHom.snd R S))
  exact RingEquiv.ofBijective (l.prod r) (by
    sorry) -- modPProdEquiv で各係数の対を戻す。Frobenius の遷移は成分ごと

/-- 概要：θ の両立：`wittVectorProdEquiv` と `preTiltProdEquiv` の下で θ_{R×S} = θ_R × θ_S（`fontaineTheta` は ghost 成分と Teichmüller で成分ごと、
mod p^n の逆極限として定義されるので各段で成分ごと）。
方針：`mk_pow_fontaineTheta` で mod p^{n+1} に落として成分ごとに比較。
規約：両同型を積から成分への向きに使う。この θ の計算には各因子の p 非単元の仮定がある。零環因子は下の積定理で別に扱う。
使われ方：核の計算。 -/
theorem fontaineTheta_prod_compat :
    letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
    letI := isAdicComplete_span_p_prod p R S
    fontaineTheta (R × S) p = ((fontaineTheta R p).prodMap (fontaineTheta S p)).comp
      ((wittVectorProdEquiv p (PreTilt R p) (PreTilt S p)).toRingHom.comp
        (WittVector.map (preTiltProdEquiv p R S).toRingHom)) := by
  sorry -- mk_pow_fontaineTheta で各 p^(n+1) の商へ射影し、Witt 係数と tilt の射影を成分ごとに比較。
        -- 両因子の p 進分離性で R × S の等式に戻す

/-- 概要：ker θ_{R×S} ≅ ker θ_R × ker θ_S（直積環のイデアル）。両方が単項（生成元 ξ_R・ξ_S）なら (ξ_R, ξ_S) が生成する単項イデアル。
方針：`fontaineTheta_prod_compat` と、直積環のイデアル I × J で I = (x)、J = (y) なら I × J = ((x, y))。
規約：—
使われ方：`isIntegralPerfectoid_prod`。 -/
theorem ker_fontaineTheta_prod_isPrincipal
    (hR : (RingHom.ker (fontaineTheta R p)).IsPrincipal) (hS : (RingHom.ker (fontaineTheta S p)).IsPrincipal) :
    letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
    letI := isAdicComplete_span_p_prod p R S
    (RingHom.ker (fontaineTheta (R × S) p)).IsPrincipal := by
  sorry

end Theta

/-! ## 主定理 -/

/-- 概要：R・S perfectoid ⇒ R × S perfectoid。
方針：どちらかが零環なら他方と同型（`isIntegralPerfectoid_of_ringEquiv`）。両方非零なら `IsIntegralPerfectoid` の右の選択肢を成分ごとに：
p 非単元（`not_isUnit_p_prod_left`）、`isAdicComplete_span_p_prod`、ϖ = (ϖ_R, ϖ_S)・a = (a_R, a_S)、`surjective_pow_p_modP_prod`、`ker_fontaineTheta_prod_isPrincipal`。
規約：—
使われ方：`isIntegralPerfectoid_finPi'`、`isIntegralPerfectoid_pi`。 -/
theorem isIntegralPerfectoid_prod (R S : Type u) [CommRing R] [CommRing S]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) : IsIntegralPerfectoid (R × S) p := by
  sorry

/-- 概要：perfectoid R の有限個のコピーの直積は perfectoid（r = 0 は零環）。`CompletedTensor.lean` の `isIntegralPerfectoid_finPi` と同じ主張の E3 非依存版。
方針：r の帰納。`(Fin (r+1) → R) ≃+* R × (Fin r → R)`（要確認：Mathlib の `RingEquiv.piFinSucc` の名前）と `isIntegralPerfectoid_prod`、`isIntegralPerfectoid_of_ringEquiv`。
規約：BS-W10 作業 A でこの証明を `isIntegralPerfectoid_finPi` の本体にする（名前は利用側 CLMST 5 本のため保つ）。
使われ方：CLMST、`finiteProduct_perfectoidization_exists_algEquiv`。 -/
theorem isIntegralPerfectoid_finPi' (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (r : ℕ) :
    IsIntegralPerfectoid (Fin r → R) p := by
  sorry

/-- 概要：添字が有限なら、perfectoid 環の族の直積 ∏ A_i は perfectoid（A6 §2.2 の ∏R_i、因子は互いに異なってよい）。
方針：`Fintype.induction_empty_option`（または Fin n との同値）と `isIntegralPerfectoid_prod`。空積は零環。
規約：Type u の族。
使われ方：A6 の `PerfdSmall` の有限積、G-A6-2。 -/
theorem isIntegralPerfectoid_pi {ι : Type u} [Fintype ι] (A : ι → Type u) [∀ i, CommRing (A i)]
    (h : ∀ i, IsIntegralPerfectoid (A i) p) : IsIntegralPerfectoid (∀ i, A i) p := by
  sorry

end SerrePositivity.BhattScholze
