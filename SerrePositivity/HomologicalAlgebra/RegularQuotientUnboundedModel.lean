module

public import SerrePositivity.CommutativeAlgebra.Koszul.UnboundedTensor
public import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange

/-!
# 正則列の商の非有界な導来テンソル模型

## 概要
任意の複体の K-flat 分解上の係数拡大を、有限 Koszul 模型に擬同型で比較し、次数を評価する。

## 方針
分解射と Koszul の増大をそれぞれテンソルに通す。後に平坦射を合成するときはホモロジーと交換する。

## 規約
BS 著者版 Construction 6.1 の入力。上に有界な導来圏への制限を置かない。

## 使われ方
実際の非有界な分解上で mod p と完全 Tor 振幅を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：Koszul の全テンソルから商への底変換の実際の鎖写像。
方針：Koszul 増大、係数加群の同型、スカラー制限の標準比較を合成する。
規約：BS 著者版 Construction 6.1 の正則列の商の模型。
使われ方：単なる数値上界ではなく実際の導来テンソルを計算する。 -/
def regularQuotientTensorComparison {r : ℕ} (x : Fin r → R)
    (hx : IsKoszulResolution x) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensor (koszulComplex x) P ⟶
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span (Set.range x)))).mapHomologicalComplex
        (.up ℤ)).obj (baseChange (Ideal.Quotient.mk (Ideal.span (Set.range x))) P) := by
  let Q := R ⧸ Ideal.span (Set.range x)
  let e := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).mapIso
    (baseChangeScalarAlgebraEquiv (R := R) (B := Q)).symm.toModuleIso
  exact cochainTensorMap (koszulAugmentation hx) (𝟙 P) ≫
    ((cochainTensorFixedRight P).mapIso e).hom ≫
      (restrictedBaseChangeComplexIso (Ideal.Quotient.mk (Ideal.span (Set.range x))) P).inv

/-- 概要：K-flat な分解上では標準比較射は擬同型。
方針：Koszul 増大の擬同型を K-flat な右因子で保ち、残りの同型を合成する。
規約：任意の非有界複体、BS 著者版 Construction 6.1。
使われ方：この模型が導来テンソルを計算すること。 -/
theorem regularQuotientTensorComparison_quasiIso {r : ℕ} (x : Fin r → R)
    (hx : IsKoszulResolution x) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : complexKFlat R P) : QuasiIso (regularQuotientTensorComparison x hx P) := by
  letI := complexKFlat_quasiIso_left R hP (koszulAugmentation hx)
  unfold regularQuotientTensorComparison
  infer_instance

/-- 概要：任意の複体に、商への底変換を計算する実在する K-flat 模型がある。
方針：半自由分解を取り、Koszul の増大の比較の擬同型性を付ける。
規約：BS 著者版 Construction 6.1。非有界な入力を含む。
使われ方：下界の評価を任意の導来入力に適用する。 -/
theorem exists_regularQuotientTensor_model {r : ℕ} (x : Fin r → R)
    (hx : IsKoszulResolution x) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (q : P ⟶ K), QuasiIso q ∧
      complexKFlat R P ∧ QuasiIso (regularQuotientTensorComparison x hx P) := by
  obtain ⟨P, q, _, hq, _, hP, _⟩ :=
    exists_unbounded_baseChange_model (Ideal.Quotient.mk (Ideal.span (Set.range x))) K
  exact ⟨P, q, hq, hP, regularQuotientTensorComparison_quasiIso x hx P hP⟩

/-- 概要：正則列の商は、任意の複体の導来テンソルの下界を列の長さだけ下げる。
方針：実際の K-flat 分解を Koszul の全テンソルに比較し、反復錐の下界を使う。
規約：BS 著者版 Construction 6.1。分解射と元の複体のホモロジーの下界を明示する。
使われ方：非有界な入力に対する Tor 振幅。 -/
theorem regularQuotientBaseChange_homology_isZero_below
    {r : ℕ} (x : Fin r → R) (hx : IsKoszulResolution x)
    {P K : CochainComplex (ModuleCat.{u} R) ℤ} (q : P ⟶ K) [QuasiIso q]
    (hP : complexKFlat R P) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i))
    (i : ℤ) (hi : i < m - (r : ℤ)) :
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span (Set.range x))) P).homology i) := by
  let Q := R ⧸ Ideal.span (Set.range x)
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  letI := (koszulTensor_resolution_comparisons x hx q hP).1
  letI := regularQuotientTensorComparison_quasiIso x hx P hP
  have h₀ : IsZero ((cochainTensor (koszulComplex x) K).homology i) :=
    (koszulComplexOn_homology_isZero_below K m hK x i hi).of_iso
      (F.mapIso (koszulCochainTensorIso x K))
  have h₁ : IsZero ((cochainTensor (koszulComplex x) P).homology i) :=
    h₀.of_iso (asIso (HomologicalComplex.homologyMap (cochainTensorMap (𝟙 (koszulComplex x)) q) i))
  have h₂ := h₁.of_iso (asIso
    (HomologicalComplex.homologyMap (regularQuotientTensorComparison x hx P) i)).symm
  have h₃ := h₂.of_iso
    ((restrictCochainHomologyIso (R := R) (C := Q) i).app
      (baseChange (Ideal.Quotient.mk (Ideal.span (Set.range x))) P)).symm
  have hs := ModuleCat.subsingleton_of_isZero h₃
  letI : Subsingleton ((baseChange (Ideal.Quotient.mk (Ideal.span (Set.range x))) P).homology i) := hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 概要：任意の複体のホモロジーの下界は平坦な係数拡大で保たれる。
方針：既存の全ての複体に対する平坦なホモロジー比較を使う。
規約：BS 著者版 Construction 6.1 の式 (6) の最後の二射。
使われ方：正則列の商の下界の評価を標的へ移す。 -/
theorem flatBaseChange_homology_isZero_below {S : Type u} [CommRing S]
    (f : R →+* S) (hf : f.Flat) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (m : ℤ) (hK : ∀ i : ℤ, i < m → IsZero (K.homology i)) :
    ∀ i : ℤ, i < m → IsZero ((baseChange f K).homology i) := by
  letI := f.toAlgebra
  letI : Module.Flat R S := hf
  intro i hi
  letI := ModuleCat.subsingleton_of_isZero (hK i hi)
  let e := flatBaseChangeHomologyEquiv R S K i
  letI : Subsingleton ((baseChange f K).homology i) := e.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end SerrePositivity
