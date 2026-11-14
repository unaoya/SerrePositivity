module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# δ 構造の導来 (p,d) 完備化 H⁰ への延長（BS 著者版 Lemma 2.18 の完備化の部分）

## 概要
W₂ の第 0 成分の核は φ で捻った第 1 座標、(p,d) 完備なら (p,φ(d)) 完備、したがって W₂ も導来完備で、
導来 (p,d) 完備化 H⁰ に δ 構造が一意に延び、p,d 導来完備な δ 環への普遍性を持つ。
BS 著者版 Lemma 2.18 の完備化への構造の延長に加え、完備な標的への δ 射を延長する補助を与える。

## 方針
原典の証明の短完全列 0 → φ_*B → W₂(B) → B → 0 と完備化の比較を形式化し、切断を完備化の普遍性で延ばす。

## 規約
エタールの部分（BS 著者版 Lemma 4.21 用）はない。古典的完備性・p 正則性・有界ねじれを仮定しない。

## 使われ方
BS 著者版 Corollary 7.3、prism の完全化、d で割る包の完備化。
-/

@[expose] public noncomputable section
universe u

/-! ## W₂の第0成分の核とFrobeniusでねじれた作用

BS 著者版 Lemma 2.18の短完全列の具体的な加群部分。
核を第1座標の加法群と同定し、基底作用がφによる作用になることを証明する。
-/

section WittTwoModuleSequence

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- 第0座標が零であるW₂元を第1座標から構成する加法射。 -/
def wittTwoZeroFirst : B →+ WittTwo p B where
  toFun x := TruncatedWittVector.mk p (fun i ↦ if i = 0 then 0 else x)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change 0 =
        ((TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else x)).out +
          (TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else y)).out).coeff 0
      rw [WittVector.add_coeff_zero]
      simp [TruncatedWittVector.out]
    · change x + y =
        ((TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else x)).out +
          (TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else y)).out).coeff 1
      rw [witt_add_coeff_one]
      simp [TruncatedWittVector.out]

/-- 零第0座標の構成の座標公式。 -/
@[simp] theorem wittTwoZeroFirst_coeff (x : B) (i : Fin 2) :
    (wittTwoZeroFirst (p := p) x).coeff i = if i = 0 then 0 else x := rfl

/-- δ切断を通じたW₂への具体的な基底射。 -/
def wittTwoBaseMap (D : DeltaStructure p A) (f : A →+* B) : A →+* WittTwo p B :=
  (wittTwoMap f).comp D.sectionHom

section ModuleSequence
variable (D : DeltaStructure p A) (f : A →+* B)

/-- 第0座標射は、δ切断を通じた基底作用について線形。 -/
def wittTwoProjectionLinear :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    WittTwo p B →ₗ[A] B := by
  letI := f.toAlgebra
  letI := (wittTwoBaseMap D f).toAlgebra
  exact {
    toAddHom := (wittTwoProjection p B).toAddMonoidHom
    map_smul' := fun r x ↦ by
      change wittTwoProjection p B (wittTwoBaseMap D f r * x) = f r * wittTwoProjection p B x
      rw [map_mul]
      congr 1
      simp only [wittTwoProjection_apply, wittTwoBaseMap, RingHom.comp_apply, wittTwoMap_coeff]
      rw [D.coeff_zero]
  }

/-- 第0座標射の核と第1座標の加法群の具体的同型。 -/
def wittTwoKernelEquiv :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    (wittTwoProjectionLinear D f).ker ≃+ B := by
  letI := f.toAlgebra
  letI := (wittTwoBaseMap D f).toAlgebra
  exact {
    toFun x := x.val.coeff 1
    invFun b := ⟨wittTwoZeroFirst b, by simp [LinearMap.mem_ker, wittTwoProjectionLinear]⟩
    left_inv x := by
      apply Subtype.ext
      apply TruncatedWittVector.ext
      intro i
      fin_cases i
      · have h : x.val.coeff 0 = 0 := x.property
        simpa using h.symm
      · rfl
    right_inv b := rfl
    map_add' := fun x y ↦ by
      change (x.val.out + y.val.out).coeff 1 = x.val.coeff 1 + y.val.coeff 1
      rw [witt_add_coeff_one]
      have hx : x.val.coeff 0 = 0 := x.property
      have hy : y.val.coeff 0 = 0 := y.property
      simp [TruncatedWittVector.out, hx, hy]
  }

/-- 核への基底作用は、φを経由した第1座標への作用に一致する。 -/
theorem wittTwoKernelEquiv_smul (r : A) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    ∀ x : (wittTwoProjectionLinear D f).ker,
      wittTwoKernelEquiv D f (r • x) = f (D.frobeniusLift r) * wittTwoKernelEquiv D f x := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  intro x
  simp only [wittTwoKernelEquiv, AddEquiv.coe_mk]
  change ((wittTwoBaseMap D f r).out * x.val.out).coeff 1 =
    f (D.frobeniusLift r) * x.val.coeff 1
  rw [witt_mul_coeff_one]
  change (wittTwoBaseMap D f r).coeff 0 ^ p * x.val.coeff 1 +
    (wittTwoBaseMap D f r).coeff 1 * x.val.coeff 0 ^ p +
    (p : B) * (wittTwoBaseMap D f r).coeff 1 * x.val.coeff 1 =
      f (D.frobeniusLift r) * x.val.coeff 1
  have hx : x.val.coeff 0 = 0 := x.property
  simp only [wittTwoBaseMap, RingHom.comp_apply,
    wittTwoMap_coeff, D.coeff_zero, hx, zero_pow (Fact.out : p.Prime).ne_zero,
    mul_zero, add_zero, DeltaStructure.delta, D.frobeniusLift_apply,
    map_add, map_mul, map_pow, map_natCast]
  ring

end ModuleSequence
end SerrePositivity.BhattScholze

end WittTwoModuleSequence

/-! ## W₂へのδ基底作用に関する実導来完備性

具体的な第0成分の核を使い、終域のf(r),f(φ(r))完備性からW₂のr完備性を得る。
(p,d)への適用ではφ(d)完備性を別途供給する必要がある。
-/

section WittTwoModuleComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- 第0座標の核は、φによる作用についての終域の実導来完備性を反映する。 -/
theorem wittTwoKernel_isModuleComplete (D : DeltaStructure p A) (f : A →+* B) (r : A)
    (hr : IsModuleComplete B (f (D.frobeniusLift r)) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A r (ModuleCat.of A (wittTwoProjectionLinear D f).ker) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  let K := (wittTwoProjectionLinear D f).ker
  let E : (ℕ → K) ≃ (ℕ → B) := Equiv.piCongrRight (fun _ ↦ (wittTwoKernelEquiv D f).toEquiv)
  have he (x : ℕ → K) : E (adicRecurrenceMap r x) =
      adicRecurrenceMap (f (D.frobeniusLift r)) (E x) := by
    funext n
    change wittTwoKernelEquiv D f (x n - r • x (n + 1)) =
      wittTwoKernelEquiv D f (x n) - f (D.frobeniusLift r) * wittTwoKernelEquiv D f (x (n + 1))
    rw [map_sub, wittTwoKernelEquiv_smul]
  have hb := (isModuleComplete_iff_recurrence_bijective B (f (D.frobeniusLift r)) _).mp hr
  apply (isModuleComplete_iff_recurrence_bijective A r _).mpr
  constructor
  · intro x y hxy
    apply E.injective
    apply hb.injective
    rw [← he, ← he, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hb.surjective (E y)
    refine ⟨E.symm z, E.injective ?_⟩
    rw [he, E.apply_symm_apply, hz]

/-- 第0座標線形射は全射。終域の各元に座標(b,0)を選ぶ。 -/
theorem wittTwoProjectionLinear_surjective (D : DeltaStructure p A) (f : A →+* B) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    Function.Surjective (wittTwoProjectionLinear D f) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  intro b
  exact ⟨TruncatedWittVector.mk p (fun i ↦ if i = 0 then b else 0), rfl⟩

/-- δ基底作用によるW₂は、f(r)とf(φ(r))で完備な終域の拡大としてr導来完備。 -/
theorem wittTwo_isModuleComplete (D : DeltaStructure p A) (f : A →+* B) (r : A)
    (hr : IsModuleComplete B (f r) (ModuleCat.of B B))
    (hφ : IsModuleComplete B (f (D.frobeniusLift r)) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A r (ModuleCat.of A (WittTwo p B)) := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  let S := (wittTwoProjectionLinear D f).shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer
    (wittTwoProjectionLinear_surjective D f)
  have hk := wittTwoKernel_isModuleComplete D f r hφ
  have hb : IsModuleComplete A r (ModuleCat.of A B) :=
    (isModuleComplete_algebraMap_iff A B r B).mp hr
  exact isModuleComplete_extension A r S hS hk hb

/-- p座標のW₂完備性には、終域のp完備性だけで十分。φ(p)=pを使う。 -/
theorem wittTwo_isModuleComplete_p (D : DeltaStructure p A) (f : A →+* B)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A (p : A) (ModuleCat.of A (WittTwo p B)) := by
  apply wittTwo_isModuleComplete D f (p : A)
  · simpa only [map_natCast] using hp
  · simpa only [map_natCast] using hp

end SerrePositivity.BhattScholze

end WittTwoModuleComplete

/-! ## δ基底像のFrobeniusに関する実導来完備性

W₂のねじれた作用に必要な、p,d完備からp,φ(d)完備への具体的接続。
既存の実導来完備性の漸化式判定を使い、古典的完備性には置き換えない。
-/

section DeltaFrobeniusComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

private theorem neumann_bijective (R : Type u) [CommRing R] (b : R)
    (M : ModuleCat.{u} R) (hb : IsModuleComplete R b M) (L : Module.End R M) :
    Function.Bijective (fun x : M ↦ x - b • L x) := by
  have hr := (isModuleComplete_iff_recurrence_bijective R b M).mp hb
  let Q : Module.End R M := LinearMap.id - b • L
  change Function.Bijective Q
  constructor
  · apply (injective_iff_map_eq_zero Q).mpr
    intro x hx
    have he : x = b • L x := sub_eq_zero.mp hx
    let z : ℕ → M := fun k ↦ (L ^ k) x
    have hz : adicRecurrenceMap b z = 0 := by
      funext k
      change (L ^ k) x - b • (L ^ (k + 1)) x = 0
      have h := congrArg (fun t ↦ (L ^ k) t) he
      rw [map_smul] at h
      rw [pow_succ, Module.End.mul_apply, h, sub_self]
    have hzero := hr.injective (hz.trans (map_zero _).symm)
    simpa [z] using congrFun hzero 0
  · intro y
    obtain ⟨z, hz⟩ := hr.surjective (fun k ↦ (L ^ k) y)
    have hshift : (fun k ↦ L (z k)) = fun k ↦ z (k + 1) := by
      apply hr.injective
      funext k
      change L (z k) - b • L (z (k + 1)) = z (k + 1) - b • z (k + 1 + 1)
      rw [← map_smul, ← map_sub]
      have h0 := congrFun hz k
      have h1 := congrFun hz (k + 1)
      change z k - b • z (k + 1) = (L ^ k) y at h0
      change z (k + 1) - b • z (k + 1 + 1) = (L ^ (k + 1)) y at h1
      rw [h0, h1, pow_succ', Module.End.mul_apply]
    refine ⟨z 0, ?_⟩
    change z 0 - b • L (z 0) = y
    rw [congrFun hshift 0]
    simpa [adicRecurrenceMap] using congrFun hz 0

private theorem complete_add (R : Type u) [CommRing R] (a b : R)
    (M : ModuleCat.{u} R) (ha : IsModuleComplete R a M) (hb : IsModuleComplete R b M) :
    IsModuleComplete R (a + b) M := by
  let P := ModuleCat.of R (ℕ → M)
  have hbP : IsModuleComplete R b P :=
    isModuleComplete_pi R b (fun _ : ℕ ↦ M) (fun _ ↦ hb)
  let E := adicRecurrenceEquiv R a M ha
  let shift : Module.End R P :=
    { toFun := fun x n ↦ x (n + 1)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : Module.End R P := E.symm.toLinearMap.comp shift
  have hL (x : P) : adicRecurrenceMap a (L x) = shift x := E.apply_symm_apply (shift x)
  have he (x : P) : adicRecurrenceMap (a + b) x = adicRecurrenceMap a (x - b • L x) := by
    rw [map_sub, map_smul, hL]
    funext n
    change x n - (a + b) • x (n + 1) = x n - a • x (n + 1) - b • x (n + 1)
    rw [add_smul]
    abel
  apply (isModuleComplete_iff_recurrence_bijective R (a + b) M).mpr
  have h := E.bijective.comp (neumann_bijective R b P hbP L)
  convert h using 1
  funext x
  exact he x

private theorem complete_of_power (R : Type u) [CommRing R] (f : R) (n : ℕ) (hn : n ≠ 0)
    (M : ModuleCat.{u} R) (h : IsModuleComplete R (f ^ n) M) : IsModuleComplete R f M := by
  let S := Localization.Away (f ^ n)
  have hu : IsUnit (algebraMap R S f) := (isUnit_pow_iff hn).mp (by
    rw [← map_pow]
    exact IsLocalization.Away.algebraMap_isUnit (f ^ n))
  have hle : Submonoid.powers (f ^ n) ≤ Submonoid.powers f :=
    Submonoid.powers_le.mpr ⟨n, rfl⟩
  let : IsLocalization (Submonoid.powers f) S :=
    IsLocalization.of_le (Submonoid.powers (f ^ n)) (Submonoid.powers f) hle (by
      rintro _ ⟨k, rfl⟩
      simpa only [map_pow] using hu.pow k)
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S
  let E : localizationObject R f ≅ localizationObject R (f ^ n) :=
    (moduleObjectFunctor R).mapIso e.toLinearEquiv.toModuleIso
  change IsComplete R f ((moduleObjectFunctor R).obj M)
  change IsComplete R (f ^ n) ((moduleObjectFunctor R).obj M) at h
  intro q g
  apply (cancel_epi E.inv).mp
  simpa only [comp_zero] using h q (E.inv ≫ g)

/-- p,f(d)導来完備な終域はf(φ(d))導来完備。pねじれ・非Noether環を許す。 -/
theorem deltaImage_frobenius_isModuleComplete {p : ℕ} [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f d) (ModuleCat.of B B)) :
    IsModuleComplete B (f (D.frobeniusLift d)) (ModuleCat.of B B) := by
  have hpow : IsModuleComplete B (f d ^ p) (ModuleCat.of B B) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
    rw [hn, pow_succ']
    exact isModuleComplete_mul_right B (f d) (f d ^ n) _ hd
  have hmul := isModuleComplete_mul_right B (p : B) (f (D.delta d)) _ hp
  have h := complete_add B (f d ^ p) ((p : B) * f (D.delta d)) _ hpow hmul
  simpa only [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast] using h

/-- p,f(φ(d))導来完備ならf(d)導来完備。完備化で逆Frobeniusを延長するための逆向き。 -/
theorem deltaImage_isModuleComplete_of_frobenius {p : ℕ} [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f (D.frobeniusLift d)) (ModuleCat.of B B)) :
    IsModuleComplete B (f d) (ModuleCat.of B B) := by
  have hm := isModuleComplete_mul_right B (p : B) (-f (D.delta d)) _ hp
  have hs := complete_add B (f (D.frobeniusLift d)) ((p : B) * -f (D.delta d)) _ hd hm
  have he : f (D.frobeniusLift d) + (p : B) * -f (D.delta d) = f d ^ p := by
    rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
    ring
  rw [he] at hs
  exact complete_of_power B (f d) p (Fact.out : p.Prime).ne_zero _ hs

end SerrePositivity.BhattScholze

end DeltaFrobeniusComplete

/-! ## p,d導来完備な終域へのW₂のδ基底作用

P2の接続。終域のφ(d)完備性はδ公式と既存の漸化式判定から証明して供給する。
古典的完備性、p正則性、ねじれの有界性を追加しない。
-/

section WittTwoPDComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- p,f(d)実導来完備な終域に対し、W₂はδ基底作用についてd実導来完備。 -/
theorem wittTwo_isModuleComplete_d (D : DeltaStructure p A) (f : A →+* B) (d : A)
    (hp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hd : IsModuleComplete B (f d) (ModuleCat.of B B)) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    IsModuleComplete A d (ModuleCat.of A (WittTwo p B)) :=
  wittTwo_isModuleComplete D f d hd (deltaImage_frobenius_isModuleComplete D f d hp hd)

end SerrePositivity.BhattScholze

end WittTwoPDComplete

/-! ## 実際の導来(p,d)完備化H⁰のBS側の作用の接続

受領したF3の対象・環構造・標準射をそのまま使う。
H⁰自身と試験環自身の作用に関する導来完備性を既存係数制限で接続する。
-/

section PDCompletionInterface

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (A : Type u) [CommRing A] (p : ℕ) (d : A)

/-- 実H⁰は自身の作用についてp導来完備。標準射からの作用と既存比較で接続する。 -/
theorem pdCompletionH0_self_complete_p :
    letI := pdCompletionCommRing A p d
    IsModuleComplete (PDCompletionH0 A p d) (p : PDCompletionH0 A p d)
      (ModuleCat.of (PDCompletionH0 A p d) (PDCompletionH0 A p d)) := by
  let := pdCompletionCommRing A p d
  let := (pdCompletionUnit A p d).toAlgebra
  let : Module A (PDCompletionH0 A p d) := (pdCompletionUnit A p d).toAlgebra.toModule
  simpa only [map_natCast] using
    (isModuleComplete_algebraMap_iff A (PDCompletionH0 A p d) (p : A)
      (PDCompletionH0 A p d)).mpr (pdCompletionH0_isComplete_p A p d)

/-- 実H⁰は自身の作用について標準像j(d)導来完備。 -/
theorem pdCompletionH0_self_complete_d :
    letI := pdCompletionCommRing A p d
    IsModuleComplete (PDCompletionH0 A p d) (pdCompletionUnit A p d d)
      (ModuleCat.of (PDCompletionH0 A p d) (PDCompletionH0 A p d)) := by
  let := pdCompletionCommRing A p d
  let := (pdCompletionUnit A p d).toAlgebra
  let : Module A (PDCompletionH0 A p d) := (pdCompletionUnit A p d).toAlgebra.toModule
  exact (isModuleComplete_algebraMap_iff A (PDCompletionH0 A p d) d
    (PDCompletionH0 A p d)).mpr (pdCompletionH0_isComplete_d A p d)

/-- 試験環自身のp,g(d)導来完備性から、実H⁰の環としての一意延長を得る。 -/
theorem existsUnique_pdCompletionRingHom (T : Type u) [CommRing T] (g : A →+* T)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∃! h : PDCompletionH0 A p d →+* T, h.comp (pdCompletionUnit A p d) = g := by
  let := g.toAlgebra
  apply pdCompletion_existsUnique_ringHom A p d T g
  · apply (isModuleComplete_algebraMap_iff A T (p : A) T).mp
    simpa only [map_natCast] using hp
  · exact (isModuleComplete_algebraMap_iff A T d T).mp hd

/-- 実H⁰からの環射は、標準基底射との合成によって決まる。 -/
theorem pdCompletionRingHom_ext (T : Type u) [CommRing T]
    (g : A →+* T) (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∀ f h : PDCompletionH0 A p d →+* T,
      f.comp (pdCompletionUnit A p d) = g →
      h.comp (pdCompletionUnit A p d) = g → f = h := by
  let := pdCompletionCommRing A p d
  obtain ⟨k, _, hu⟩ := existsUnique_pdCompletionRingHom A p d T g hp hd
  intro f h hf hh
  exact (hu f hf).trans (hu h hh).symm

end SerrePositivity.BhattScholze

end PDCompletionInterface

/-! ## 実際の導来(p,d)完備化H⁰へのδ構造の一意延長

BS 著者版 Lemma 2.18の完備化への適用部分。
受領F3の環普遍性とW₂の実導来完備性から切断を延長する。
p正則性・古典的完備性・有界ねじれを仮定しない。
-/

section DeltaPDCompletion

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実際のH⁰に、標準射をδ射とするδ構造が一意に存在する（BS 著者版 Lemma 2.18 の末尾の導来完備化の帰結で (p,d)・H⁰ の場合）。 -/
theorem existsUnique_deltaPDCompletionStructure (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    ∃! E : DeltaStructure p (PDCompletionH0 A p d), D.IsDeltaHom E (pdCompletionUnit A p d) := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  obtain ⟨s, hs, hsu⟩ := pdCompletion_existsUnique_ringHom A p d (WittTwo p H)
    (wittTwoBaseMap D j) (wittTwo_isModuleComplete_p D j hpH)
    (wittTwo_isModuleComplete_d D j d hpH hdH)
  have hproj : (wittTwoProjection p H).comp s = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · rw [RingHom.comp_assoc, hs]
      apply RingHom.ext
      intro x
      simp only [RingHom.comp_apply, wittTwoProjection_apply, wittTwoBaseMap,
        wittTwoMap_coeff, D.coeff_zero]
    · exact RingHom.id_comp j
  let E : DeltaStructure p H :=
    { sectionHom := s
      coeff_zero := fun x ↦ RingHom.congr_fun hproj x }
  have hE : D.IsDeltaHom E j :=
    (D.isDeltaHom_iff_sectionHom_comp E j).mpr hs.symm
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  have hb : E'.sectionHom.comp j = wittTwoBaseMap D j :=
    ((D.isDeltaHom_iff_sectionHom_comp E' j).mp hE').symm
  have he : E'.sectionHom = s := hsu E'.sectionHom hb
  apply DeltaStructure.ext
  intro x
  exact congrArg (fun z : WittTwo p H ↦ z.coeff 1) (RingHom.congr_fun he x)

/-- 実際の(p,d)完備化H⁰に選んだ唯一のδ構造（BS 著者版 Lemma 2.18 の末尾の導来完備化の帰結で (p,d)・H⁰ の構成）。 -/
def deltaPDCompletionStructure (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    DeltaStructure p (PDCompletionH0 A p d) :=
  (existsUnique_deltaPDCompletionStructure D d).choose

/-- 元のKoszul標準射は、選んだδ構造へのδ射。 -/
theorem pdCompletionUnit_isDeltaHom (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    D.IsDeltaHom (deltaPDCompletionStructure D d) (pdCompletionUnit A p d) :=
  (existsUnique_deltaPDCompletionStructure D d).choose_spec.1

/-- 標準射がδ射になる任意のδ構造は、選んだ構造に一致する。 -/
theorem deltaPDCompletionStructure_unique (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    ∀ E : DeltaStructure p (PDCompletionH0 A p d),
      D.IsDeltaHom E (pdCompletionUnit A p d) → E = deltaPDCompletionStructure D d :=
  (existsUnique_deltaPDCompletionStructure D d).choose_spec.2

end SerrePositivity.BhattScholze

end DeltaPDCompletion

/-! ## 実際の導来(p,d)完備化H⁰のδ普遍性

任意のδ基底・pねじれを許す試験δ環について、実導来完備性を明示して一意延長する。
prism性・perfectoid性・全射性はこの普遍性には含めない。
-/

section DeltaPDCompletionUniversal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- 実H⁰からの環延長は、基底δ射の延長なら自動的にδ射になる。 -/
theorem pdCompletionRingHom_isDeltaHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∀ h : PDCompletionH0 A p d →+* T, h.comp (pdCompletionUnit A p d) = g →
      (deltaPDCompletionStructure D d).IsDeltaHom E h := by
  let := pdCompletionCommRing A p d
  intro h hh
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let DH := deltaPDCompletionStructure D d
  let F := (wittTwoMap h).comp DH.sectionHom
  let G := E.sectionHom.comp h
  have hj := (D.isDeltaHom_iff_sectionHom_comp DH j).mp (pdCompletionUnit_isDeltaHom D d)
  have hF : F.comp j = wittTwoBaseMap D g := by
    apply RingHom.ext
    intro x
    apply TruncatedWittVector.ext
    intro i
    change (wittTwoMap h (DH.sectionHom (j x))).coeff i =
      (wittTwoMap g (D.sectionHom x)).coeff i
    rw [wittTwoMap_coeff, wittTwoMap_coeff]
    have hn := congrArg (fun z : WittTwo p H ↦ z.coeff i) (RingHom.congr_fun hj x)
    simp only [RingHom.comp_apply] at hn
    rw [← hn, wittTwoMap_coeff]
    exact RingHom.congr_fun hh ((D.sectionHom x).coeff i)
  have hG : G.comp j = wittTwoBaseMap D g := by
    change (E.sectionHom.comp h).comp j = (wittTwoMap g).comp D.sectionHom
    rw [RingHom.comp_assoc, hh]
    exact ((D.isDeltaHom_iff_sectionHom_comp E g).mp hg).symm
  obtain ⟨s, _, hu⟩ := pdCompletion_existsUnique_ringHom A p d (WittTwo p T)
    (wittTwoBaseMap D g) (wittTwo_isModuleComplete_p D g hp)
    (wittTwo_isModuleComplete_d D g d hp hd)
  apply (DH.isDeltaHom_iff_sectionHom_comp E h).mpr
  exact (hu F hF).trans (hu G hG).symm

/-- 任意のp,g(d)実導来完備δ環へ、実H⁰からのδ延長が一意に存在する。 -/
theorem existsUnique_deltaPDCompletionHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∃! h : PDCompletionH0 A p d →+* T,
      (deltaPDCompletionStructure D d).IsDeltaHom E h ∧ h.comp (pdCompletionUnit A p d) = g := by
  let := pdCompletionCommRing A p d
  obtain ⟨h, hh, hu⟩ := existsUnique_pdCompletionRingHom A p d T g hp hd
  refine ⟨h, ⟨pdCompletionRingHom_isDeltaHom D d E g hg hp hd h hh, hh⟩, ?_⟩
  intro k hk
  exact hu k hk.2

/-- 実H⁰から試験δ環への具体的な一意延長環射。 -/
def deltaPDCompletionLift (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    PDCompletionH0 A p d →+* T :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose

/-- 選んだ具体的延長はδ射。 -/
theorem deltaPDCompletionLift_isDeltaHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionStructure D d).IsDeltaHom E (deltaPDCompletionLift D d E g hg hp hd) :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose_spec.1.1

/-- 選んだ具体的延長は元のKoszul標準射との合成で基底射gに一致する。 -/
theorem deltaPDCompletionLift_comp_unit (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionLift D d E g hg hp hd).comp (pdCompletionUnit A p d) = g :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose_spec.1.2

end SerrePositivity.BhattScholze

end DeltaPDCompletionUniversal

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.18" (partial := special) "後半の「導来 (p,d) 完備化（H⁰）への δ 構造の延長」だけ。I 完全エタール代数（Elkik・van der Kallen）の部分は未・不要 ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：existsUnique_deltaPDCompletionHom（完備化の射の普遍性。原文は構造の延長を述べるため補助として module docstring に置く。） ／ DOC1 照合：ok 2 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaPDCompletionStructure
attribute [cite BS19 "Lemma 2.18" (partial := special) "後半の「導来 (p,d) 完備化（H⁰）への δ 構造の延長」だけ。I 完全エタール代数（Elkik・van der Kallen）の部分は未・不要 ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：existsUnique_deltaPDCompletionHom（完備化の射の普遍性。原文は構造の延長を述べるため補助として module docstring に置く。） ／ DOC1 照合：ok 2 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_deltaPDCompletionStructure
