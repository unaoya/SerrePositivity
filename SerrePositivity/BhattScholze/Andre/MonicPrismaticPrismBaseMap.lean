module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCandidateComparison
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-!
# André E1・E2：多項式 prism 候補の標準基底射

## 概要

多項式族の既存台環候補を完全 prism として束ね、元の係数射が生成元とイデアルを保つことを示す。
BS Rem 7.15（著者版 p.62）の perfectoid 商の実係数射の準備。

## 方針

一般除算候補の完全 prism を使い、標準 δ 射を合成する。商射は代表元で比較する。
原典の Prop 7.11 を使う証明とは異なる具体的係数射による計算。

## 規約

任意多項式族を扱い、モニック性・正次数・有限性を要求しない。

## 使われ方

生成元の正則性と実生成元商の標準 perfectoid 候補への比較に使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "W" => PCompletedDeltaDivision E (MvPolynomial.C d) r
local notation "j" => pCompletedDeltaDivisionMap E (MvPolynomial.C d) r

/-- 概要：既存多項式候補台環を、選択生成元を持つ prism として束ねる。
方針：一般関係族の除算候補を独立変数の評価族に適用する。
規約：係数環の d の distinguished 性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の標準 perfectoid 商の基底射。 -/
def polynomialPrism (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    OrientedPrism p T := by
  let := polynomialPrismCommRing D d f
  exact divisionPrism E (MvPolynomial.C d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：既存多項式 prism 候補の δ 構造は完全。
方針：一般関係族の完全 prism 構成の既存結果を使う。
規約：多項式族の平坦性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の商の perfectoid 性と生成元の比較。 -/
theorem polynomialPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (polynomialPrism D d f hd).deltaStructure.IsPerfect := by
  let := polynomialPrismCommRing D d f
  exact divisionPrism_isPerfect E (MvPolynomial.C d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：raw 包から候補台環への標準射は δ 射。
方針：p 進完備 δ 完全化と実 PD 完備化単位の δ 射性を合成する。
規約：任意多項式族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の候補の標準係数射を prism 射にする。 -/
theorem polynomialPrismRawMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (F).IsDeltaHom (polynomialPrism D d f hd).deltaStructure (polynomialPrismRawMap D d f) := by
  let := polynomialPrismCommRing D d f
  exact (pdCompletionUnit_isDeltaHom (pCompletedDeltaDivisionStructure E (MvPolynomial.C d) r)
    (j (MvPolynomial.C d))).comp (pCompletedDeltaPerfectionMap_isDeltaHom F)

/-- 概要：元の A から候補への標準係数射は δ 射。
方針：多項式係数包含、raw 除算射、候補射の δ 射性を合成する。
規約：係数射は前工程の具体的な標準射である。
使われ方：BS Rem 7.15（著者版 p.62）の標準 prism 射。 -/
theorem polynomialPrismCoefficientMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    D.IsDeltaHom (polynomialPrism D d f hd).deltaStructure (polynomialPrismCoefficientMap D d f) := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismRawMap_isDeltaHom D d f hd).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

/-- 概要：元の d の像は候補 prism の選択生成元そのもの。
方針：標準係数射と候補生成元の定義の一致による。
規約：任意多項式族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の生成元商の比較。 -/
theorem polynomialPrismCoefficientMap_generator (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    polynomialPrismCoefficientMap D d f d = (polynomialPrism D d f hd).generator := rfl

/-- 概要：元の生成元イデアルの標準像は候補 prism のイデアル全体に一致する。
方針：主イデアルの像と生成元の標準像を使う。
規約：イデアルの包含だけでなく等式を示す。
使われ方：BS Rem 7.15（著者版 p.62）の標準 perfectoid 商の同定。 -/
theorem polynomialPrismCoefficientMap_ideal (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (Ideal.span {d}).map (polynomialPrismCoefficientMap D d f) =
      (polynomialPrism D d f hd).ideal := by
  let := polynomialPrismCommRing D d f
  rw [Ideal.map_span, Set.image_singleton, polynomialPrismCoefficientMap_generator D d f hd]
  rfl

/-- 概要：標準係数射による候補台環の A 代数構造。
方針：具体的係数射の toAlgebra を使う。
規約：利用箇所で局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の通常生成元商の係数作用。 -/
@[instance_reducible] def polynomialPrismCoefficientAlgebra :
    letI := polynomialPrismCommRing D d f
    Algebra A T := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismCoefficientMap D d f).toAlgebra

/-- 概要：元の prism から既存多項式 prism 候補への標準 prism 射。
方針：標準係数 δ 射と生成元イデアルの像の等式を束ねる。
規約：基底 prism の生成元の distinguished 性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商の基底射。 -/
def polynomialPrismBaseHom (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (f : σ → Polynomial A) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    OrientedPrism.Hom P (polynomialPrism P.deltaStructure P.generator f hd) := by
  let := polynomialPrismCommRing P.deltaStructure P.generator f
  refine ⟨polynomialPrismCoefficientMap P.deltaStructure P.generator f,
    polynomialPrismCoefficientMap_isDeltaHom P.deltaStructure P.generator f hd, ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  change (Ideal.span {P.generator}).map _ ≤ _
  exact (polynomialPrismCoefficientMap_ideal P.deltaStructure P.generator f hd).le

/-- 概要：標準 prism 射の誘導商射は既存 perfectoid 候補の基底射と一致する。
方針：元の生成元商の代表元で比較する。
規約：同じ候補への具体的な二つの係数射を照合する。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商の p 完全忠実平坦性。 -/
theorem polynomialPrismBaseHom_quotientMap (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (f : σ → Polynomial A) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    (polynomialPrismBaseHom P hd f).quotientMap =
      polynomialPerfectoidCandidateBaseMap P.deltaStructure P.generator f hd := by
  let := polynomialPrismCommRing P.deltaStructure P.generator f
  apply RingHom.ext
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

end SerrePositivity.BhattScholze.Andre
