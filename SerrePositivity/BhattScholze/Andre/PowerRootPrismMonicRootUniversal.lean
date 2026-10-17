module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialDeltaUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionUniversal

/-!
# André E1・E2：互換な rank 1 根データによる実完備化の普遍射

## 概要

元の raw 実完備化から試験 prism への射を、無限根入力 δ 射の指定を使わず、
基底 δ 射・互換な rank 1 根列・モニック入力の可除性から一意に作る。
BS Rem 7.15（著者版 p.62）の絶対 envelope 比較へ向けた入力射の具体化。

## 方針

有理指数による無限根評価で δ 射を構成し、raw 割り算と実完備化の普遍性へ渡す。
原典とは異なる具体的な単項式評価と Witt 座標による証明。

## 規約

源の prism 商の p 正則性や入力のモニック性はこの普遍射には不要。
剰余上の根列の試験 prism 内への一意持上げは引き続き別工程。

## 使われ方

既存の指定 δ 入力射を、基底と実根列のデータから作る。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
section Evaluation
variable {R : Type u} [CommRing R] (p₀ : ℕ) (hp₀ : 0 < p₀)
variable {B : Type u} [CommRing B] (k : R →+* B)
variable (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p₀ = ρ n)

/-- 概要：無限根評価と通常変数での多項式入力は指定した第零根での通常評価と一致。
方針：環射と多項式評価の可換性を係数公式・第零変数公式で計算する。
規約：入力多項式のモニック性や次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の分子の可除性を元の方程式で表す。 -/
theorem powerRootPolynomialEval_baseMap (g : Polynomial R) :
    powerRootPolynomialEval p₀ hp₀ k ρ hρ (powerRootPolynomialBaseMap R p₀ hp₀ g) =
      g.eval₂ k (ρ 0) := by
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, powerRootPolynomialEval_variable]
  have hc : (powerRootPolynomialEval p₀ hp₀ k ρ hρ).comp
      (algebraMap R (PowerRootPolynomial R p₀ hp₀)) = k := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p₀ hp₀ k ρ hρ
  rw [hc]

end Evaluation

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


/-- 概要：基底 δ 射と互換な rank 1 根列から実完備化への一意な射を作る。
方針：無限根評価 δ 射に raw 実完備化の普遍性を適用し、一意性を係数・根上で確認する。
規約：根列は試験 prism の台環内に与え、剰余からの持上げは仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の指定入力 δ 射を具体的データで置き換える。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hδρ : ∀ n, Q.deltaStructure.delta (ρ n) = 0)
    (hroot : Q.generator ∣ f.eval₂ k (ρ 0)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, F (uL (jL (powerRootPolynomialVariable A p hp n))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let g := powerRootPolynomialEval p hp k ρ hρ
  have hg : (E).IsDeltaHom Q.deltaStructure g :=
    powerRootPolynomialEval_isDeltaHom p hW.p_mul_injective W.deltaStructure
      Q.deltaStructure k hk ρ hρ hδρ
  have hdg : g dP = Q.generator := (powerRootPolynomialEval_coeff p hp k ρ hρ W.generator).trans hd
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact Q.generator_regular
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    change g dP ∣ g (powerRootMonicPDInput p f)
    rw [hdg]
    unfold powerRootMonicPDInput
    exact (powerRootPolynomialEval_baseMap p hp k ρ hρ f).symm ▸ hroot
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact Q.complete_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k
    rw [hF.2]
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp k ρ hρ
  · intro n
    exact (RingHom.congr_fun hF.2 (powerRootPolynomialVariable A p hp n)).trans
      (powerRootPolynomialEval_variable p hp k ρ hρ n)
  · intro K hK
    apply hu K
    refine ⟨hK.1, ?_⟩
    apply powerRootPolynomial_ringHom_ext p hp
    · have hkg : (K.comp ((uL).comp jL)).comp (algebraMap A P) = k := hK.2.1
      apply RingHom.ext
      intro r
      exact (RingHom.congr_fun hkg r).trans (powerRootPolynomialEval_coeff p hp k ρ hρ r).symm
    · intro n
      exact (hK.2.2 n).trans (powerRootPolynomialEval_variable p hp k ρ hρ n).symm

/-- 概要：p 正則な試験 prism の互換根列から、実完備化への射が一意に存在する。
方針：導来 p 完備性と p 正則性から p 進分離性を得て、根の δ 条件を自動で供給する。
規約：p 正則性は試験 prism の台環に課し、源の prism 商には課さない。
使われ方：BS Rem 7.15（著者版 p.62）の実根データによる比較射。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_p_regular_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (hpB : Function.Injective (fun x : B => (p : B) * x))
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : Q.generator ∣ f.eval₂ k (ρ 0)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, F (uL (jL (powerRootPolynomialVariable A p hp n))) = ρ n := by
  let := Q.isAdicComplete_p_of_regular hpB
  exact existsUnique_powerRootPrismMonicCompletionHom_of_roots W hW f Q k hk hd ρ hρ
    (compatiblePowerRoots_delta_eq_zero p Q.deltaStructure ρ hρ) hroot

end SerrePositivity.BhattScholze.Andre
