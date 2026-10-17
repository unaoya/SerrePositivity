module

public import SerrePositivity.BhattScholze.Andre.PolynomialPerfectoidCandidate
public import SerrePositivity.BhattScholze.DeltaPDCompletionPerfectionComparison
public import SerrePositivity.BhattScholze.DeltaPerfectionPDCompletionComparison
public import SerrePositivity.BhattScholze.DeltaAlgebraPerfectionCocone

/-!
# André E1・E2：PD 先行 δ 完全化と多項式 prism 候補の標準比較

## 概要

raw f/d 包の PD 完備化・δ 完全化・PD 完備化による環は、既存の多項式 prism 候補と
元の A 係数射を保って同型。BS Rem 7.15（著者版 p.62）の二つの候補の比較。

## 方針

既存の一般 PD 完備化挿入比較と p 進完備化挿入比較を合成する。
原典の Prop 7.11 を用いる証明とは異なる具体的な標準係数射の計算。

## 規約

任意多項式族で比較し、モニック性・正次数・有限性は使わない。

## 使われ方

PD 先行構成で証明した完全忠実平坦性を、根方程式を持つ既存の prism 候補へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "ι" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "r₀" => RingHom.comp (RingHom.comp (pdCompletionUnit C p x)
  (deltaPerfectionOf G 0)) v
local notation "W" => PCompletedDeltaDivision E (MvPolynomial.C d) r
local notation "j" => pCompletedDeltaDivisionMap E (MvPolynomial.C d) r
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r

/-- 概要：raw f/d 包から既存の多項式 prism 台環候補への標準環射。
方針：既存の p 進完備 δ 完全化射と実 PD 完備化単位を合成する。
規約：平坦性を仮定しない具体的な射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の二つの標準 raw 係数射の比較。 -/
def polynomialPrismRawMap :
    letI := polynomialPrismCommRing D d f
    Raw →+* T := by
  let := polynomialPrismCommRing D d f
  exact (pdCompletionUnit W p (j (MvPolynomial.C d))).comp (pCompletedDeltaPerfectionMap F)

/-- 概要：元の A から既存の多項式 prism 台環候補への標準係数射。
方針：raw 候補射と raw 包の元の A 係数射を合成する。
規約：perfectoid 商を取る前の係数射である。
使われ方：BS Rem 7.15（著者版 p.62）の候補の完全忠実平坦性を述べる。 -/
def polynomialPrismCoefficientMap :
    letI := polynomialPrismCommRing D d f
    A →+* T := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismRawMap D d f).comp c

/-- 概要：PD 先行完全化の実環は、既存の多項式 prism 台環候補と環同型。
方針：二つの一般完備化挿入比較を合成する。
規約：比較の両側の具体的な環構造を局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の既存候補へ平坦性を移す。 -/
def monicPrismaticPDPerfectionCandidateEquiv :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    H ≃+* T := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  exact (deltaPDCompletionPerfectionEquiv F z).symm.trans (deltaPerfectionPDCompletionEquiv F z)

/-- 概要：候補の環同型と逆同型は、実際の完備化 δ 構造と両立する。
方針：二つの一般完備化挿入比較の両方向の δ 射性を合成する。
規約：distinguished 性やモニック性を使わない一般環比較として述べる。
使われ方：BS Rem 7.15（著者版 p.62）の同じ完全 δ 候補への接続。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_isDeltaHom :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing (PCompletedDeltaPerfection F) p
      (pCompletedDeltaPerfectionMap F z)
    letI := polynomialPrismCommRing D d f
    (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z))
      (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom ∧
    (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
      (pCompletedDeltaPerfectionMap F z)).IsDeltaHom
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x)
      (monicPrismaticPDPerfectionCandidateEquiv D d f).symm.toRingHom := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p
    (pCompletedDeltaPerfectionMap F z)
  let := polynomialPrismCommRing D d f
  exact ⟨((deltaPerfectionPDCompletionEquiv_spec F z).1).comp
      (deltaPDCompletionPerfectionEquiv_spec F z).2.1,
    ((deltaPDCompletionPerfectionEquiv_spec F z).1).comp
      (deltaPerfectionPDCompletionEquiv_spec F z).2.1⟩

/-- 概要：候補比較は raw 包からの両標準射を保つ。
方針：一般比較の逆射と順射の標準 raw 射公式を順に使う。
規約：任意の raw 元で一致を確認する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A 作用の線形比較への入力。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_comp_raw :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom.comp r₀ =
      polynomialPrismRawMap D d f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  apply RingHom.ext
  intro a
  have h : (deltaPDCompletionPerfectionEquiv F z).symm (r₀ a) =
      pdCompletionUnit (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
        (deltaPerfectionOf F 0 a) :=
    RingHom.congr_fun (deltaPDCompletionPerfectionInverse_spec F z).2 a
  change deltaPerfectionPDCompletionEquiv F z
    ((deltaPDCompletionPerfectionEquiv F z).symm (r₀ a)) = polynomialPrismRawMap D d f a
  rw [h]
  exact RingHom.congr_fun (deltaPerfectionPDCompletionEquiv_spec F z).2.2 a

/-- 概要：候補の環同型は元の A の標準係数射を保つ。
方針：raw 係数射を保つ公式と合成の結合律を使う。
規約：係数射の取り替えを行わない。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数環に関する忠実平坦性の移送。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_comp_coefficient :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom.comp ((r₀).comp c) =
      polynomialPrismCoefficientMap D d f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  rw [← RingHom.comp_assoc, monicPrismaticPDPerfectionCandidateEquiv_comp_raw]
  rfl

/-- 概要：二つの候補の元の A 係数作用は、同じ環同型による線形同型を持つ。
方針：標準係数射を保つ公式と積の保存からスカラー作用の可換性を示す。
規約：元の係数環 A 上の同型を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の既存候補の完全忠実平坦性。 -/
def monicPrismaticPDPerfectionCandidateModuleIso :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    baseChangeScalarModule ((r₀).comp c) ≅
      baseChangeScalarModule (polynomialPrismCoefficientMap D d f) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  let e := monicPrismaticPDPerfectionCandidateEquiv D d f
  let M := baseChangeScalarModule ((r₀).comp c)
  let N := baseChangeScalarModule (polynomialPrismCoefficientMap D d f)
  let eA : M ≃ₗ[A] N :=
    { e.toAddEquiv with
      map_smul' := by
        intro a y
        change H at y
        change e ((r₀).comp c a * y) = polynomialPrismCoefficientMap D d f a * e y
        rw [map_mul]
        exact congrArg (fun h => h * e y)
          (RingHom.congr_fun (monicPrismaticPDPerfectionCandidateEquiv_comp_coefficient D d f) a) }
  exact eA.toModuleIso

end SerrePositivity.BhattScholze.Andre
