module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# perfectoid 環の有限直積は perfectoid（G-A6-12、E3 非依存の直接証明）

## 概要
R・S が perfectoid（`IsIntegralPerfectoid`）なら R × S も perfectoid。帰納で `Fin r → R`（r = 0 は零環）を得る。
BS 著者版 Theorem 3.10 の prism 表示に関わる perfectoid 環の有限直積の補題。完備テンソルと有限図式の計算で使う。

## 方針
p 進完備性・p = aϖ^p・mod p の Frobenius 全射を成分ごとに示す。
Fontaine 核の単項性は、ModP・Perfection（PreTilt）・Witt ベクトルが
有限直積と可換であること（係数ごとの計算）と θ の両立から、ker θ_{R×S} = ker θ_R × ker θ_S = ((ξ_R, ξ_S))。
`isIntegralPerfectoid_of_compatible_p_roots`（Perfectoid/Fontaine.lean）は p 正則を仮定するので一般には使わない。

## 規約
零環を含める（`IsIntegralPerfectoid` の左の選択肢）。
`Fact (¬IsUnit (p : R × S))` と `IsAdicComplete` の直積のインスタンスは補題で供給し、定理の中で `letI`。

## 使われ方
A6 §2.2（R → ∏R_i への置き換え、`PerfdSmall` の有限積）、G-A6-2、CLMST の `isIntegralPerfectoid_finPi` の利用側（名前を保つ）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.BhattScholze

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime]

/-! ## 直積の基本的な両立 -/

section Prod
variable (R S : Type u) [CommRing R] [CommRing S]

omit [Fact p.Prime] in
/-- 概要：どちらかの因子で p が単元でなければ直積でも単元でない。
方針：単元の射影。
規約：—
使われ方：`Fact (¬IsUnit (p : R × S))` の供給。 -/
theorem not_isUnit_p_prod_left (h : ¬ IsUnit (p : R)) : ¬ IsUnit (p : R × S) := by
  intro hu
  exact h (by simpa using hu.map (RingHom.fst R S))

omit [Fact p.Prime] in
/-- 概要：p 進完備性は有限直積で保たれる（`IsHausdorff`・`IsPrecomplete` を成分ごとに）。
方針：Mathlib に直積版が見当たらないので成分ごとの合同で書く（`Ideal.span {(p : R × S)}` の冪は成分ごとの冪の直積）。
規約：—
使われ方：直積の `IsAdicComplete`。 -/
theorem isAdicComplete_span_p_prod
    [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : R × S)}) (R × S) := by
  have split (x y : R × S) (n : ℕ) :
      (x ≡ y [SMOD (Ideal.span {(p : R × S)} ^ n • ⊤ : Ideal (R × S))]) ↔
      (x.1 ≡ y.1 [SMOD (Ideal.span {(p : R)} ^ n • ⊤ : Ideal R)]) ∧
      (x.2 ≡ y.2 [SMOD (Ideal.span {(p : S)} ^ n • ⊤ : Ideal S)]) := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, prod_dvd_iff]
    rfl
  refine { haus' := ?_, prec' := ?_ }
  · exact fun x hx ↦ Prod.ext
      (IsHausdorff.haus' (I := Ideal.span {(p : R)}) x.1 fun n ↦ ((split x 0 n).mp (hx n)).1)
      (IsHausdorff.haus' (I := Ideal.span {(p : S)}) x.2 fun n ↦ ((split x 0 n).mp (hx n)).2)
  · intro f hf
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : R)}) (fun n ↦ (f n).1)
      fun {m n} h ↦ ((split (f m) (f n) m).mp (hf h)).1
    obtain ⟨b, hb⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : S)}) (fun n ↦ (f n).2)
      fun {m n} h ↦ ((split (f m) (f n) m).mp (hf h)).2
    exact ⟨(a, b), fun n ↦ (split _ _ n).mpr ⟨ha n, hb n⟩⟩

/-- 概要：(R × S)/p ≅ R/p × S/p。
方針：代表元の対で全射性を示し、p による整除性を成分ごとに判定して単射性を示す。
規約：`ModP O p := O ⧸ span {p}`（Mathlib）。
使われ方：Frobenius の全射性、PreTilt の直積。 -/
def modPProdEquiv : ModP (R × S) p ≃+* ModP R p × ModP S p := by
  let f := (modPMap p (RingHom.fst R S)).prod (modPMap p (RingHom.snd R S))
  refine RingEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨a, b⟩, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.mem_span_singleton, prod_dvd_iff]
    have ha : Ideal.Quotient.mk _ a = (0 : ModP R p) := congrArg Prod.fst hx
    have hb : Ideal.Quotient.mk _ b = (0 : ModP S p) := congrArg Prod.snd hx
    exact ⟨Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha),
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hb)⟩
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (a, b), rfl⟩

omit [Fact p.Prime] in
/-- 概要：Frobenius の全射性は有限直積で保たれる。
方針：`modPProdEquiv` と成分ごと。
規約：—
使われ方：`isIntegralPerfectoid_prod`。 -/
theorem surjective_pow_p_modP_prod
    (hR : Function.Surjective (fun x : ModP R p ↦ x ^ p))
    (hS : Function.Surjective (fun x : ModP S p ↦ x ^ p)) :
    Function.Surjective (fun x : ModP (R × S) p ↦ x ^ p) := by
  intro x
  let e := modPProdEquiv p R S
  obtain ⟨a, ha⟩ := hR (e x).1
  obtain ⟨b, hb⟩ := hS (e x).2
  refine ⟨e.symm (a, b), e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact Prod.ext ha hb

/-- 概要：Perfection は有限直積と可換（Frobenius に沿う逆極限は有限積と可換。係数 `Perfection.coeff` ごとに）。
方針：`Perfection.map` の射影の対で射を作り、係数で単射・全射。
規約：A・B は標数 p。
使われ方：PreTilt の直積。 -/
def perfectionProdEquiv (A B : Type u) [CommRing A] [CommRing B] [CharP A p] [CharP B p] :
    Perfection (A × B) p ≃+* Perfection A p × Perfection B p := by
  letI := Prod.charP A B p
  let f := (Perfection.map p (RingHom.fst A B)).prod (Perfection.map p (RingHom.snd A B))
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Perfection.ext fun n ↦ Prod.ext
      (congrArg (fun z ↦ Perfection.coeff A p n (Prod.fst z)) h)
      (congrArg (fun z ↦ Perfection.coeff B p n (Prod.snd z)) h)
  · rintro ⟨a, b⟩
    exact ⟨⟨fun n ↦ (a.val n, b.val n), fun n ↦ Prod.ext (a.property n) (b.property n)⟩,
      Prod.ext (Perfection.ext fun _ ↦ rfl) (Perfection.ext fun _ ↦ rfl)⟩

/-- 概要：Witt ベクトルは有限直積と可換：W(A × B) ≅ W(A) × W(B)。
方針：`WittVector.map` の射影の対（環準同型）。逆は係数ごとに `(a_n, b_n)` を置く。`map_coeff` で両立。
規約：Mathlib に直積の同型はないので係数で書く。
使われ方：θ の直積。 -/
def wittVectorProdEquiv (A B : Type u) [CommRing A] [CommRing B] :
    WittVector p (A × B) ≃+* WittVector p A × WittVector p B :=
  RingEquiv.ofBijective
    ((WittVector.map (RingHom.fst A B)).prod (WittVector.map (RingHom.snd A B))) (by
    constructor
    · intro x y h
      exact WittVector.ext fun n ↦ Prod.ext
        (congrArg (fun z ↦ (Prod.fst z).coeff n) h)
        (congrArg (fun z ↦ (Prod.snd z).coeff n) h)
    · rintro ⟨a, b⟩
      exact ⟨WittVector.mk p fun n ↦ (a.coeff n, b.coeff n),
        Prod.ext (WittVector.ext fun _ ↦ rfl) (WittVector.ext fun _ ↦ rfl)⟩)

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
  let e := modPProdEquiv p R S
  letI := Prod.charP (ModP R p) (ModP S p) p
  let pe := RingEquiv.ofRingHom (Perfection.map p e.toRingHom) (Perfection.map p e.symm.toRingHom)
    (RingHom.ext fun x ↦ Perfection.ext fun n ↦ e.apply_symm_apply (x.val n))
    (RingHom.ext fun x ↦ Perfection.ext fun n ↦ e.symm_apply_apply (x.val n))
  exact pe.trans (perfectionProdEquiv p (ModP R p) (ModP S p))

/-- 概要：`wittVectorProdEquiv` と `preTiltProdEquiv` の下で θ_{R×S} = θ_R × θ_S。
方針：既存の `fontaineTheta_natural` を二つの射影に適用する。
規約：両同型を積から成分への向きに使う。この θ の計算には各因子の p 非単元の仮定がある。零環因子は下の積定理で別に扱う。
使われ方：核の計算。 -/
theorem fontaineTheta_prod_compat :
    letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
    letI := isAdicComplete_span_p_prod p R S
    fontaineTheta (R × S) p = ((fontaineTheta R p).prodMap (fontaineTheta S p)).comp
      ((wittVectorProdEquiv p (PreTilt R p) (PreTilt S p)).toRingHom.comp
        (WittVector.map (preTiltProdEquiv p R S).toRingHom)) := by
  let : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
  let := isAdicComplete_span_p_prod p R S
  exact RingHom.ext fun x ↦ Prod.ext
    (RingHom.congr_fun (fontaineTheta_natural p (RingHom.fst R S)) x).symm
    (RingHom.congr_fun (fontaineTheta_natural p (RingHom.snd R S)) x).symm

/-- 概要：ker θ_{R×S} ≅ ker θ_R × ker θ_S（直積環のイデアル）。両方が単項（生成元 ξ_R・ξ_S）なら (ξ_R, ξ_S) が生成する単項イデアル。
方針：`fontaineTheta_prod_compat` と、直積環のイデアル I × J で I = (x)、J = (y) なら I × J = ((x, y))。
規約：—
使われ方：`isIntegralPerfectoid_prod`。 -/
theorem ker_fontaineTheta_prod_isPrincipal
    (hR : (RingHom.ker (fontaineTheta R p)).IsPrincipal)
    (hS : (RingHom.ker (fontaineTheta S p)).IsPrincipal) :
    letI : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
    letI := isAdicComplete_span_p_prod p R S
    (RingHom.ker (fontaineTheta (R × S) p)).IsPrincipal := by
  let : Fact (¬ IsUnit (p : R × S)) := ⟨not_isUnit_p_prod_left p R S Fact.out⟩
  let := isAdicComplete_span_p_prod p R S
  let t := preTiltProdEquiv p R S
  let w := RingEquiv.ofBijective (WittVector.map (p := p) t.toRingHom)
    ⟨WittVector.map_injective _ t.injective, WittVector.map_surjective _ t.surjective⟩
  let e := w.trans (wittVectorProdEquiv p (PreTilt R p) (PreTilt S p))
  rw [fontaineTheta_prod_compat p R S]
  change (RingHom.ker (((fontaineTheta R p).prodMap (fontaineTheta S p)).comp
    e.toRingHom)).IsPrincipal
  rw [← RingHom.comap_ker, RingHom.ker_prodMap]
  obtain ⟨a, ha⟩ := hR.principal
  obtain ⟨b, hb⟩ := hS.principal
  rw [ha, hb, ← Ideal.span_prod (iff_of_true (Set.singleton_nonempty a) (Set.singleton_nonempty b)),
    Set.singleton_prod_singleton]
  change ((Ideal.span {(a, b)}).comap e).IsPrincipal
  rw [← Ideal.map_symm e, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

end Theta

/-! ## 主定理 -/

/-- 概要：R・S perfectoid ⇒ R × S perfectoid。
方針：どちらかが零環なら他方と同型（`isIntegralPerfectoid_of_ringEquiv`）。両方非零なら `IsIntegralPerfectoid` の右の選択肢を成分ごとに：
p 非単元、p 進完備、ϖ = (ϖ_R, ϖ_S) と a = (a_R, a_S)、Frobenius の全射性、Fontaine 核の単項性を示す。
規約：—
使われ方：`isIntegralPerfectoid_finPi`。 -/
theorem isIntegralPerfectoid_prod (R S : Type u) [CommRing R] [CommRing S]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) :
    IsIntegralPerfectoid (R × S) p := by
  rcases hR with hR | ⟨hpR, hcR, ⟨πR, uR, heR⟩, hsR, hkR⟩
  · let := hR
    exact isIntegralPerfectoid_of_ringEquiv p (RingEquiv.zeroRingProd S R) hS
  rcases hS with hS | ⟨hpS, hcS, ⟨πS, uS, heS⟩, hsS, hkS⟩
  · let := hS
    exact isIntegralPerfectoid_of_ringEquiv p (RingEquiv.prodZeroRing R S)
      (.inr ⟨hpR, hcR, ⟨πR, uR, heR⟩, hsR, hkR⟩)
  let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
  let : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
  let := hcR
  let := hcS
  exact .inr ⟨not_isUnit_p_prod_left p R S hpR, isAdicComplete_span_p_prod p R S,
    ⟨(πR, πS), MulEquiv.prodUnits.symm (uR, uS), Prod.ext heR heS⟩,
    surjective_pow_p_modP_prod p R S hsR hsS, ker_fontaineTheta_prod_isPrincipal p R S hkR hkS⟩

/-- 有限個の perfectoid 環 R の直積は perfectoid。空積は零環。 -/
theorem isIntegralPerfectoid_finPi
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ) : IsIntegralPerfectoid (Fin r → R) p := by
  induction r with
  | zero => exact .inl inferInstance
  | succ r ih =>
    let e : (Fin (r + 1) → R) ≃+* R × (Fin r → R) :=
      { (Fin.consEquiv fun _ ↦ R).symm with
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
    exact isIntegralPerfectoid_of_ringEquiv p e.symm (isIntegralPerfectoid_prod p R _ hR ih)

/-- Any specified universal perfectoidization of the finite product is its
original unit as an algebra equivalence over the original base. -/
theorem finiteProduct_perfectoidization_exists_algEquiv
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ e : (Fin r → R) ≃ₐ[R] C, e.toAlgHom = f := by
  obtain ⟨e, he⟩ := (isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id.exists_equiv p hf
  have hef : e.toRingHom = f.toRingHom := by simpa only [RingHom.comp_id] using he
  let e' : (Fin r → R) ≃ₐ[R] C := AlgEquiv.ofRingEquiv (f := e) fun s => by
    change e.toRingHom (algebraMap R (Fin r → R) s) = algebraMap R C s
    rw [hef]
    exact f.commutes s
  exact ⟨e', by ext x; exact RingHom.congr_fun hef x⟩

end SerrePositivity.BhattScholze
