module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
概要：KST §5、Stacks 051R の一般自由性に使う単元先頭係数の標準単項式基底。
方針：多項式の除法の余りを標準単項式の部分加群に取り、イデアル商への全単射を示す。
規約：先頭次数を覆う族は実際のイデアル元からなり、未証明の基底の存在を仮定しない。
使われ方：有限個の先頭係数を反転した後の代数の自由性。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：指定した先頭単項式のいずれでも割れない単項式次数の集合。
方針：座標毎の次数の不等式を全て否定する。
規約：KST §5、Stacks 051R、単項式順序自体の大小とは区別する。
使われ方：商の基底の添字と、除法の余りの台の指定。
-/
def standardMonomialDegrees {σ R : Type u} [CommRing R]
    (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  {d | ∀ g ∈ G, ¬m.degree g ≤ d}

/--
概要：標準単項式に台を持つ多項式を、指定イデアルによる商へ送る線形写像。
方針：部分加群の包含と商写像のスカラー制限を合成する。
規約：KST §5、Stacks 051R、定義には先頭次数の被覆条件は不要。
使われ方：標準単項式基底の実際の比較同型。
-/
def standardMonomialQuotientMap {σ R : Type u} [CommRing R]
    (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R)) (H : Ideal (MvPolynomial σ R)) :
    (MvPolynomial.restrictSupport R (standardMonomialDegrees m G)) →ₗ[R]
      (MvPolynomial σ R ⧸ H) :=
  (H.mkQ.restrictScalars R).comp (MvPolynomial.restrictSupport R
    (standardMonomialDegrees m G)).subtype

/--
概要：全非零イデアル元の先頭次数を覆う族の標準単項式は、商で一次独立。
方針：核の非零多項式の先頭次数が、標準性と被覆性に同時に反することを使う。
規約：KST §5、Stacks 051R、先頭係数の単元性は単射性には不要。
使われ方：商の標準単項式比較の単射性。
-/
theorem standardMonomialQuotientMap_injective
    {σ R : Type u} [CommRing R] (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R))
    (H : Ideal (MvPolynomial σ R))
    (hcover : ∀ h ∈ H, h ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree h) :
    Function.Injective (standardMonomialQuotientMap m G H) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro r hr
  have hrH : r.val ∈ H := Ideal.Quotient.eq_zero_iff_mem.mp hr
  have hr0 : r.val = 0 := by
    by_contra hr0
    obtain ⟨g, hg, hgr⟩ := hcover r.val hrH hr0
    have hstd := ((MvPolynomial.mem_restrictSupport_iff R).mp r.property) (m.degree_mem_support hr0)
    exact hstd g hg hgr
  exact Subtype.ext hr0

/--
概要：単元先頭係数を持つイデアル元の族の標準単項式は、イデアル商を生成する。
方針：Mathlib の除法アルゴリズムの余りを標準台に取り、引いた項のイデアルへの所属を確認する。
規約：KST §5、Stacks 051R、この生成性には先頭次数の被覆条件は不要。
使われ方：商の標準単項式比較の全射性。
-/
theorem standardMonomialQuotientMap_surjective
    {σ R : Type u} [CommRing R] (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R))
    (H : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, g ∈ H)
    (hu : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    Function.Surjective (standardMonomialQuotientMap m G H) := by
  classical
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, r, hfr, hdeg, hstd⟩ := m.div (b := fun g : G => g.val)
    (fun g => hu g.val g.property) f
  have hr : r ∈ MvPolynomial.restrictSupport R (standardMonomialDegrees m G) := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro d hd g hg
    exact hstd d hd ⟨g, hg⟩
  have hqH : Finsupp.linearCombination (MvPolynomial σ R) (fun g : G => g.val) q ∈ H := by
    rw [Finsupp.linearCombination_apply]
    exact H.sum_mem (fun g hg => H.mul_mem_left (q g) (hG g.val g.property))
  refine ⟨⟨r, hr⟩, ?_⟩
  change H.mkQ r = H.mkQ f
  rw [hfr, map_add]
  have hq0 : H.mkQ (Finsupp.linearCombination (MvPolynomial σ R) (fun g : G => g.val) q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hqH
  rw [hq0, zero_add]

/--
概要：単元先頭係数と先頭次数の被覆を持つ族について、標準台の部分加群は商と実際に線形同型。
方針：構成した標準商写像の単射性と全射性を組み合わせる。
規約：KST §5、Stacks 051R、基礎環の整域性や Noether 性は不要。
使われ方：標準単項式の基底を商へ移す。
-/
def standardMonomialQuotientEquiv
    {σ R : Type u} [CommRing R] (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R))
    (H : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, g ∈ H)
    (hu : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ h ∈ H, h ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree h) :
    (MvPolynomial.restrictSupport R (standardMonomialDegrees m G)) ≃ₗ[R]
      (MvPolynomial σ R ⧸ H) :=
  LinearEquiv.ofBijective (standardMonomialQuotientMap m G H)
    ⟨standardMonomialQuotientMap_injective m G H hcover,
      standardMonomialQuotientMap_surjective m G H hG hu⟩

/--
概要：先頭係数が単元で先頭次数を覆う族の標準単項式から、イデアル商の実際の基底を得る。
方針：標準台の部分加群の基底を構成した線形同型で商へ移す。
規約：KST §5、Stacks 051R、基底の添字は実際に標準単項式の集合。
使われ方：一般自由性で反転した係数環上の商を自由にする。
-/
def standardMonomialQuotientBasis
    {σ R : Type u} [CommRing R] (m : MonomialOrder σ) (G : Finset (MvPolynomial σ R))
    (H : Ideal (MvPolynomial σ R)) (hG : ∀ g ∈ G, g ∈ H)
    (hu : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ h ∈ H, h ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree h) :
    Module.Basis (standardMonomialDegrees m G) R (MvPolynomial σ R ⧸ H) :=
  (MvPolynomial.basisRestrictSupport R (standardMonomialDegrees m G)).map
    (standardMonomialQuotientEquiv m G H hG hu hcover)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
