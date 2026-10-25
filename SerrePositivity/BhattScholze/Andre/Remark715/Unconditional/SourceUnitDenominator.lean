module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionUnitDenominator
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalizationSaturation
public import Mathlib.RingTheory.Localization.Ideal

/-!
# 単元分母での実源 δ 射の可逆性

## 概要
BS Rem 7.15（著者版 p.62）の実源を、分母が単元となる係数環上で調べる。

## 方針
自由 δ 射の一意性から分母の乗法性を示し、逆単元で逆射を構成する。

## 規約
元の自由 δ 環とその実源射を用い、係数環の p 正則性を仮定しない。

## 使われ方
raw 包の p 正則性を調べる際の、Frobenius 安定局所化側の比較を供給する。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 概要：分母を掛ける実源 δ 射の合成は、積を掛ける実源射。
方針：係数と初期変数上で計算し、自由 δ 射の一意性を使う。
規約：分母の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の逆射。 -/
theorem unconditionalDeltaDivisionSourceMap_comp (D : DeltaStructure p A) (d e : A) :
    (deltaDivisionSourceMap (σ := σ) D d).comp (deltaDivisionSourceMap D e) =
      deltaDivisionSourceMap D (e * d) := by
  let F := relativeFreeDeltaStructure σ D
  let g := (deltaDivisionSourceMap (σ := σ) D d).comp (deltaDivisionSourceMap D e)
  have hg : F.IsDeltaHom F g := by
    intro x
    change deltaDivisionSourceMap D d (deltaDivisionSourceMap D e (F.delta x)) = _
    rw [deltaDivisionSourceMap_isDeltaHom D e, deltaDivisionSourceMap_isDeltaHom D d]
    rfl
  have hC : g.comp MvPolynomial.C = MvPolynomial.C := by
    ext r
    simp [g, RingHom.comp_apply, deltaDivisionSourceMap_C]
  have hX (s : σ) : g (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (e * d) * MvPolynomial.X (s, 0) := by
    simp [g, RingHom.comp_apply, deltaDivisionSourceMap_X, deltaDivisionSourceMap_C,
      map_mul, mul_assoc]
  exact (existsUnique_relativeFreeDeltaHom D F MvPolynomial.C
    (relativeFreeDeltaStructure_C_isDeltaHom σ D)
    (fun s => MvPolynomial.C (e * d) * MvPolynomial.X (s, 0))).unique
      ⟨hg, hC, hX⟩ ⟨deltaDivisionSourceMap_isDeltaHom D _,
        by apply RingHom.ext; intro r; exact deltaDivisionSourceMap_C D _ r,
        by intro s; exact deltaDivisionSourceMap_X D _ s 0⟩

/-- 概要：単元を分母とする実源射の環同型。
方針：逆単元の実源射との合成を計算する。
規約：元の自由 δ 環そのものの自己同型。
使われ方：BS Rem 7.15（著者版 p.62）の分母可逆な部分。 -/
def unconditionalDeltaDivisionSourceUnitEquiv (D : DeltaStructure p A) (d : Aˣ) :
    RelativeFreeDeltaRing (R := A) σ ≃+* RelativeFreeDeltaRing (R := A) σ :=
  { deltaDivisionSourceMap D (d : A) with
    invFun := deltaDivisionSourceMap D ((d⁻¹ : Aˣ) : A)
    left_inv := by
      intro x
      have h := unconditionalDeltaDivisionSourceMap_comp (σ := σ) D
        ((d⁻¹ : Aˣ) : A) (d : A)
      rw [Units.mul_inv, deltaDivisionSourceMap_one] at h
      exact DFunLike.congr_fun h x
    right_inv := by
      intro x
      have h := unconditionalDeltaDivisionSourceMap_comp (σ := σ) D
        (d : A) ((d⁻¹ : Aˣ) : A)
      rw [Units.inv_mul, deltaDivisionSourceMap_one] at h
      exact DFunLike.congr_fun h x }

/-- 概要：分母が単元なら元の実源射は全単射。
方針：逆単元から構成した環同型の全単射性を使う。
規約：同型に置き換えず、元の環射について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の局所化後の実源。 -/
theorem unconditionalDeltaDivisionSourceMap_bijective_of_isUnit
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) :
    Function.Bijective (deltaDivisionSourceMap (σ := σ) D d) := by
  obtain ⟨u, rfl⟩ := hd
  exact (unconditionalDeltaDivisionSourceUnitEquiv (σ := σ) D u).bijective

/-- 概要：係数 δ 射の多項式への拡大も、実自由 δ 構造を保つ。
方針：自由 δ 評価射と、全 δ 座標上で一致することを示す。
規約：係数射の単射性・平坦性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の係数局所化との両立。 -/
theorem unconditionalRelativeFreeMap_isDeltaHom
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom (relativeFreeDeltaStructure σ E)
      (MvPolynomial.map q) := by
  let g := relativeFreeDeltaEval (relativeFreeDeltaStructure σ E) (MvPolynomial.C.comp q)
    (fun s : σ => MvPolynomial.X (s, 0))
  have hg : (relativeFreeDeltaStructure σ D).IsDeltaHom
      (relativeFreeDeltaStructure σ E) g := by
    apply relativeFreeDeltaEval_isDeltaHom
    intro x
    change MvPolynomial.C (q (D.delta x)) = _
    rw [hq x, ← relativeFreeDeltaStructure_delta_C]
    rfl
  have he : g = MvPolynomial.map q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [g, RingHom.comp_apply]
    · rintro ⟨s, n⟩
      rw [show g (MvPolynomial.X (s, n)) =
          (relativeFreeDeltaStructure σ E).delta^[n] (MvPolynomial.X (s, 0)) from
            relativeFreeDeltaEval_X _ _ _ _ _, MvPolynomial.map_X]
      exact (relativeFreeDeltaHom_X_iterates E (relativeFreeDeltaStructure σ E)
        (RingHom.id _) (fun _ => rfl) s n).symm
  rw [he] at hg
  exact hg

/-- 概要：実源の分母倍射は係数 δ 射と可換。
方針：係数と初期生成元を比較し、δ 射の一意性で全座標へ延長する。
規約：元の多項式係数射を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の実源の局所化比較。 -/
theorem unconditionalDeltaDivisionSourceMap_natural
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    (q : A →+* B) (hq : D.IsDeltaHom E q) (d : A) :
    (MvPolynomial.map q).comp (deltaDivisionSourceMap (σ := σ) D d) =
      (deltaDivisionSourceMap E (q d)).comp (MvPolynomial.map q) := by
  let F := relativeFreeDeltaStructure σ D
  let G := relativeFreeDeltaStructure σ E
  let l := (MvPolynomial.map q).comp (deltaDivisionSourceMap (σ := σ) D d)
  let r := (deltaDivisionSourceMap (σ := σ) E (q d)).comp (MvPolynomial.map q)
  have hl : F.IsDeltaHom G l := by
    intro x
    change MvPolynomial.map q (deltaDivisionSourceMap D d (F.delta x)) = _
    rw [deltaDivisionSourceMap_isDeltaHom D d,
      unconditionalRelativeFreeMap_isDeltaHom D E q hq]
    rfl
  have hr : F.IsDeltaHom G r := by
    intro x
    change deltaDivisionSourceMap E (q d) (MvPolynomial.map q (F.delta x)) = _
    rw [unconditionalRelativeFreeMap_isDeltaHom D E q hq,
      deltaDivisionSourceMap_isDeltaHom E (q d)]
    rfl
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, deltaDivisionSourceMap_C]
  · rintro ⟨s, n⟩
    change l (MvPolynomial.X (s, n)) = r (MvPolynomial.X (s, n))
    rw [relativeFreeDeltaHom_X_iterates D G l hl s n,
      relativeFreeDeltaHom_X_iterates D G r hr s n]
    congr 1
    simp [l, r, RingHom.comp_apply, deltaDivisionSourceMap_X]

/-- 概要：Frobenius 安定化した分母局所化では、実源射は全単射。
方針：局所化の δ 構造と分母の単元性を使う。
規約：任意の実局所化環に適用でき、p 正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分母可逆部分の比較。 -/
theorem unconditionalDeltaDivisionSourceMap_bijective_localization
    (D : DeltaStructure p A) (d : A) (B : Type w) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B] :
    Function.Bijective (deltaDivisionSourceMap (σ := σ)
      (D.localization (D.frobeniusDenominators (Submonoid.powers d)) B
        (D.frobeniusDenominators_stable (Submonoid.powers d))) (algebraMap A B d)) := by
  apply unconditionalDeltaDivisionSourceMap_bijective_of_isUnit
  exact IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩

/-- 概要：mod p 係数射上で d が単元なら、安定化した全分母も単元。
方針：Frobenius の像が p 冪になることを反復し、乗法的閉包へ延長する。
規約：終域の δ 構造は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の安定局所化と通常の mod p 局所化の比較。 -/
theorem unconditionalFrobeniusDenominators_isUnit_mod_prime
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A)
    (q : A →+* B) (hp : q (p : A) = 0) (hd : IsUnit (q d))
    (s : D.frobeniusDenominators (Submonoid.powers d)) : IsUnit (q s) := by
  have hφ (x : A) : q (D.frobeniusLift x) = (q x) ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
  have hiter (r : Submonoid.powers d) (n : ℕ) :
      IsUnit (q ((D.frobeniusLift : A → A)^[n] r)) := by
    induction n with
    | zero =>
      obtain ⟨m, hm⟩ := r.property
      change IsUnit (q (r : A))
      rw [← hm, map_pow]
      exact hd.pow m
    | succ n ih =>
      rw [Function.iterate_succ_apply', hφ]
      exact ih.pow p
  exact Submonoid.closure_induction
    (fun x hx => by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
    (by simp)
    (fun x y _ _ hx hy => by rw [map_mul]; exact hx.mul hy) s.property

/-- 概要：安定化した分母集合の mod p 像は、元の分母像の冪集合そのもの。
方針：Frobenius 反復像が p 冪へ移ることと、元の分母集合の包含を使う。
規約：任意の p を零に送る環射について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の二つの実局所化の同定。 -/
theorem unconditionalFrobeniusDenominators_map_mod_prime
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A)
    (q : A →+* B) (hp : q (p : A) = 0) :
    (D.frobeniusDenominators (Submonoid.powers d)).map q.toMonoidHom =
      Submonoid.powers (q d) := by
  have hφ (x : A) : q (D.frobeniusLift x) = (q x) ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
  have hiter (r : Submonoid.powers d) (n : ℕ) :
      q ((D.frobeniusLift : A → A)^[n] r) ∈ Submonoid.powers (q d) := by
    induction n with
    | zero =>
      obtain ⟨m, hm⟩ := r.property
      change q (r : A) ∈ Submonoid.powers (q d)
      rw [← hm, map_pow]
      exact pow_mem (Submonoid.mem_powers _) m
    | succ n ih =>
      rw [Function.iterate_succ_apply', hφ]
      exact pow_mem ih p
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact Submonoid.closure_induction
      (fun x hx => by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
      (by simp)
      (fun x y _ _ hx hy => by rw [map_mul]; exact mul_mem hx hy) hs
  · rw [← Submonoid.map_powers q d]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, D.le_frobeniusDenominators (Submonoid.powers d) hx, rfl⟩

/-- 概要：実安定局所化の mod p 商は、元の mod p 商の d 局所化。
方針：局所化とイデアル商の可換性に、分母集合の像の等式を適用する。
規約：終域は元の局所化環 B の実イデアル商。
使われ方：BS Rem 7.15（著者版 p.62）の二つの局所化を同じ対象上で比較する。 -/
theorem unconditionalSaturatedLocalization_mod_prime_isLocalizationAway
    (D : DeltaStructure p A) (d : A) (B : Type w) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B] :
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {(p : A)}) d)
      (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hp : q (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  change IsLocalization (Submonoid.powers (q d)) _
  rw [← unconditionalFrobeniusDenominators_map_mod_prime D d q hp]
  exact IsLocalization.of_surjective (D.frobeniusDenominators (Submonoid.powers d)) B
    q Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk ((Ideal.span {(p : A)}).map (algebraMap A B)))
    Ideal.Quotient.mk_surjective rfl (by simp [q])

end SerrePositivity.BhattScholze.Andre
