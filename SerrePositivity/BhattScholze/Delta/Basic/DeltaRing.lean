module


public meta import SerrePositivity.Util.Citation
public import Mathlib.RingTheory.WittVector.Truncated
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.Tactic.FinCases

/-!
# δ 環の定義と基本操作（BS 著者版 §2.1：BS 著者版 Definition 2.1、BS 著者版 Remark 2.2・Remark 2.4）

## 概要
δ 構造を W₂ への環準同型切断として定義し（BS 著者版 Remark 2.4）、
BS 著者版 Definition 2.1 の恒等式との同値、Frobenius 持ち上げとの対応（BS 著者版 Remark 2.2）、
δ 射とその言い換えを与える。W₂ の関手性と単元判定、環同型による δ 構造の移送、δ 安定部分環への制限も含む。
BS 著者版 Definition 2.1・Remark 2.2・Remark 2.4。
W₂ 切断での δ 射の判定と、Frobenius と可換な射の判定を、BS 著者版 Remark 2.4 と Remark 2.2 の構造の対応に付随する補題として扱う。

## 方針
W₂ の和・積の第 1 座標の公式（共通基盤）を切断に当てて恒等式を読む。p で割る式は使わない。

## 規約
p ねじれ・零環を許す。δ 構造は型クラスではなくデータ `DeltaStructure p A`。

## 使われ方
BS のすべての δ 環の議論の土台。
-/

@[expose] public noncomputable section
universe u v w

/-! ## δ環のW₂切断による表現

BS 著者版 Remark 2.4の切断を採用する。pねじれの消去を仮定せず、
MathlibのWitt環を使ってδ構造とFrobenius持上げを表す。
-/

section DeltaRing

namespace SerrePositivity.BhattScholze

variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]

/-- 長さ2のWitt環（BS 著者版 Remark 2.4 の長さ 2 の Witt 環）。
  δ構造を表す切断の行先として用いる。 -/
abbrev WittTwo := TruncatedWittVector p 2 A

/-- W₂の第0成分射。切断の条件を環準同型で表すため、Mathlibの切断から降下する。 -/
def wittTwoProjection : WittTwo p A →+* A :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      exact (WittVector.mem_ker_truncate 2 x).mp hx 0 (by decide)⟩

/-- 第0成分射はWitt座標の第0成分である。 -/
@[simp] theorem wittTwoProjection_apply (x : WittTwo p A) :
    wittTwoProjection p A x = x.coeff 0 := by
  change x.out.coeff 0 = x.coeff 0
  exact TruncatedWittVector.coeff_out x 0

/-- W₂の第1ghost成分。x₀^p+p x₁という式はpねじれの有無によらず環準同型。 -/
def wittTwoFrobenius : WittTwo p A →+* A :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨WittVector.ghostComponent 1, by
      intro x hx
      have h := (WittVector.mem_ker_truncate 2 x).mp hx
      change WittVector.ghostComponent 1 x = 0
      rw [witt_ghostComponent_one, h 0 (by decide), h 1 (by decide)]
      simp [Nat.Prime.ne_zero (Fact.out : p.Prime)]⟩

/-- 第1ghost成分の座標式。δからFrobenius持上げを計算する際に使う。 -/
@[simp] theorem wittTwoFrobenius_apply (x : WittTwo p A) :
    wittTwoFrobenius p A x = x.coeff 0 ^ p + (p : A) * x.coeff 1 := by
  change WittVector.ghostComponent 1 x.out = _
  rw [witt_ghostComponent_one]
  simp [TruncatedWittVector.out, add_comm]

/-- δ構造はW₂の第0成分射の環準同型切断（BS 著者版 Remark 2.4 の切断による定義、Definition 2.1 の恒等式と同値、序論の Remark 1.2）。
追加のp正則性を要求せず、零環も含む。prismのδ構造に用いる。 -/
structure DeltaStructure where
  sectionHom : A →+* WittTwo p A
  coeff_zero : ∀ x, (sectionHom x).coeff 0 = x

namespace DeltaStructure
variable {p A}

/-- 切断の第1座標からδ写像を取り出す。 -/
def delta (D : DeltaStructure p A) (x : A) : A := (D.sectionHom x).coeff 1

/-- 切断と第0成分射の合成は恒等射。 -/
@[simp] theorem projection_comp (D : DeltaStructure p A) :
    (wittTwoProjection p A).comp D.sectionHom = RingHom.id A := by
  ext x
  exact (wittTwoProjection_apply p A _).trans (D.coeff_zero x)

/-- δは零を零に送る。W₂の零の座標から従う。 -/
@[simp] theorem delta_zero (D : DeltaStructure p A) : D.delta 0 = 0 := by
  simp [delta]

/-- δは1を零に送る。W₂の単位の第1座標から従う。 -/
@[simp] theorem delta_one (D : DeltaStructure p A) : D.delta 1 = 0 := by
  change (D.sectionHom 1).coeff 1 = 0
  rw [map_one]
  change (1 : WittVector p A).coeff 1 = 0
  exact WittVector.one_coeff_eq_of_pos p A 1 (by decide)

/-- δの積公式（BS 著者版 Definition 2.1 の積の恒等式）。
  既存のWitt第1積係数公式を適用し、
pねじれの消去を使わずに証明する。 -/
theorem delta_mul (D : DeltaStructure p A) (x y : A) :
    D.delta (x * y) = x ^ p * D.delta y + D.delta x * y ^ p +
      (p : A) * D.delta x * D.delta y := by
  change (D.sectionHom (x * y)).coeff 1 = _
  rw [map_mul]
  change ((D.sectionHom x).out * (D.sectionHom y).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, D.coeff_zero, delta]

/-- δの加法公式（BS 著者版 Definition 2.1 の加法の恒等式）。
  共通Witt加法係数を再利用し、
pねじれのある環でも繰上りをTeichmüller和の第1座標として計算する。 -/
theorem delta_add (D : DeltaStructure p A) (x y : A) :
    D.delta (x + y) = D.delta x + D.delta y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  change (D.sectionHom (x + y)).coeff 1 = _
  rw [map_add]
  change ((D.sectionHom x).out + (D.sectionHom y).out).coeff 1 = _
  rw [witt_add_coeff_one]
  simp [TruncatedWittVector.out, D.coeff_zero, delta]

/-- δの加法補正項は整数係数多項式の評価。環内でpを除算しない。 -/
theorem delta_add_polynomial (D : DeltaStructure p A) (x y : A) :
    D.delta (x + y) = D.delta x + D.delta y +
      MvPolynomial.eval₂ (Int.castRingHom A) (fun i : Fin 2 ↦ if i = 0 then x else y)
        (wittAdditionCarry p) := by
  rw [eval_wittAdditionCarry]
  exact D.delta_add x y

/-- δ構造のFrobenius持上げ（BS 著者版 Remark 2.2 の Frobenius 持ち上げの構成、序論の Remark 1.2）。
  第1ghost成分と切断を合成する。 -/
def frobeniusLift (D : DeltaStructure p A) : A →+* A :=
  (wittTwoFrobenius p A).comp D.sectionHom

/-- Frobenius持上げの式φ(x)=x^p+pδ(x)。pねじれがあっても成立する。 -/
@[simp] theorem frobeniusLift_apply (D : DeltaStructure p A) (x : A) :
    D.frobeniusLift x = x ^ p + (p : A) * D.delta x := by
  simp [frobeniusLift, D.coeff_zero, delta]

/-- 同じδ写像を持つ切断は一致する。第0座標は切断条件、第1座標は仮定を使う。 -/
@[ext] theorem ext {D E : DeltaStructure p A} (h : ∀ x, D.delta x = E.delta x) : D = E := by
  have hs : D.sectionHom = E.sectionHom := by
    ext x i
    fin_cases i
    · exact (D.coeff_zero x).trans (E.coeff_zero x).symm
    · exact h x
  cases D
  cases E
  cases hs
  rfl

/-- distinguished元はδ(d)が単元である元（BS 著者版 Definition 2.19）。 -/
def IsDistinguished (D : DeltaStructure p A) (d : A) : Prop := IsUnit (D.delta d)

/-- 完全δ構造はFrobenius持上げが全単射である構造（BS 著者版 Definition 2.26）。
  完全prismの条件に用いる。 -/
def IsPerfect (D : DeltaStructure p A) : Prop := Function.Bijective D.frobeniusLift

/-- 環準同型がδと可換であるという条件。pねじれを持つ環でもδの情報を保持する。 -/
def IsDeltaHom {B : Type v} [CommRing B] (D : DeltaStructure p A)
    (E : DeltaStructure p B) (f : A →+* B) : Prop := ∀ x, f (D.delta x) = E.delta (f x)

/-- δと可換な環準同型はFrobenius持上げとも可換。座標式と準同型則で証明する。 -/
theorem IsDeltaHom.map_frobeniusLift {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) (x : A) : f (D.frobeniusLift x) = E.frobeniusLift (f x) := by
  simp only [frobeniusLift_apply, map_add, map_mul, map_pow, map_natCast, hf x]

/-- δ射はdistinguished元を保存する（BS 著者版 Definition 2.19 の直後の保存性）。
  δの可換性と単元の像を使う。 -/
theorem IsDeltaHom.map_isDistinguished {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) {d : A} (hd : D.IsDistinguished d) : E.IsDistinguished (f d) := by
  change IsUnit (E.delta (f d))
  rw [← hf d]
  exact hd.map f

/-- 恒等環準同型はδと可換。δ環の射の単位に使う。 -/
theorem isDeltaHom_id (D : DeltaStructure p A) : D.IsDeltaHom D (RingHom.id A) :=
  fun _ ↦ rfl

/-- δと可換な環準同型の合成もδと可換。 -/
theorem IsDeltaHom.comp {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {F : DeltaStructure p C}
    {f : A →+* B} {g : B →+* C} (hg : E.IsDeltaHom F g) (hf : D.IsDeltaHom E f) :
    D.IsDeltaHom F (g.comp f) := by
  intro x
  change g (f (D.delta x)) = F.delta (g (f x))
  rw [hf x, hg (f x)]

/-- δ射である環同型の逆もδ射。完全性やp正則性は要求しない。 -/
theorem IsDeltaHom.symm {B : Type v} [CommRing B] {D : DeltaStructure p A}
    {E : DeltaStructure p B} {e : A ≃+* B} (he : D.IsDeltaHom E e.toRingHom) :
    E.IsDeltaHom D e.symm.toRingHom := by
  intro x
  apply e.injective
  change e (e.symm (E.delta x)) = e (D.delta (e.symm x))
  have h := he (e.symm x)
  change e (D.delta (e.symm x)) = E.delta (e (e.symm x)) at h
  simpa only [e.apply_symm_apply] using h.symm

/-- pを零に送る任意の環準同型上で、φはp乗と一致する。
特にA/(p)上のFrobeniusを持ち上げるというBS BS 著者版 Remark 2.2の主張を与える。 -/
theorem map_frobeniusLift_of_map_p_eq_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (f : A →+* B) (hp : f (p : A) = 0) (x : A) :
    f (D.frobeniusLift x) = f x ^ p := by
  rw [frobeniusLift_apply, map_add, map_mul, map_pow, hp, zero_mul, add_zero]

/-- p正則な環では、Frobenius持上げが一致するδ構造は一致する。
p倍を消去してδを復元し、切断の座標による外延性を使う（BS 著者版 Remark 2.2の一意性）。 -/
theorem eq_of_frobeniusLift_eq
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    {D E : DeltaStructure p A} (h : D.frobeniusLift = E.frobeniusLift) : D = E := by
  apply ext
  intro x
  apply hp
  apply add_left_cancel (a := x ^ p)
  simpa only [frobeniusLift_apply] using DFunLike.congr_fun h x

/-- 終域でpが正則なら、Frobeniusと可換な環準同型はδとも可換。
pねじれを持つ終域についてこの逆向きは主張しない。 -/
theorem isDeltaHom_of_map_frobeniusLift {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} (f : A →+* B)
    (hp : Function.Injective (fun x : B ↦ (p : B) * x))
    (hf : ∀ x, f (D.frobeniusLift x) = E.frobeniusLift (f x)) : D.IsDeltaHom E f := by
  intro x
  apply hp
  apply add_left_cancel (a := f x ^ p)
  simpa only [frobeniusLift_apply, map_add, map_mul, map_pow, map_natCast] using hf x

/-- δで安定なイデアル。商δ環とδ閉包の構成（BS 著者版 Lemma 2.9）の入力に使う。 -/
def IsStable (D : DeltaStructure p A) (I : Ideal A) : Prop :=
  ∀ x ∈ I, D.delta x ∈ I

/-- δ射の核はδで安定。δが零を零に送ることを使う、商構成の必要条件。 -/
theorem IsDeltaHom.isStable_ker {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) : D.IsStable (RingHom.ker f) := by
  intro x hx
  change f (D.delta x) = 0
  rw [hf x, show f x = 0 from hx, delta_zero]

end DeltaStructure
end SerrePositivity.BhattScholze

end DeltaRing

/-! ## 長さ2のWitt環の係数写像

環準同型をW₂の各座標に適用する。δ切断の自然性や商構成で共通に使う。
-/

section WittTwoMap

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環準同型をW₂の各座標に適用する射。δ切断の自然性を表すために使う。 -/
def wittTwoMap (f : A →+* B) : WittTwo p A →+* WittTwo p B :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate 2).comp (WittVector.map f), by
      intro x hx
      change (WittVector.truncate 2) (WittVector.map f x) = 0
      apply (WittVector.mem_ker_truncate (p := p) 2 (WittVector.map f x)).mpr
      intro i hi
      rw [WittVector.map_coeff, (WittVector.mem_ker_truncate 2 x).mp hx i hi, map_zero]⟩

/-- W₂上の射は各Witt座標に元の環準同型を適用する。 -/
@[simp] theorem wittTwoMap_coeff (f : A →+* B) (x : WittTwo p A) (i : Fin 2) :
    (wittTwoMap (p := p) f x).coeff i = f (x.coeff i) := by
  change ((WittVector.truncate 2) (WittVector.map f x.out)).coeff i = _
  rw [WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_out]

end SerrePositivity.BhattScholze

end WittTwoMap

/-! ## 長さ2のWitt環の単元判定

δ局所化のW₂切断を延長するためのBS専用補題。
第0座標と第1ghost成分が単元なら、明示的な逆元を構成する。
基底のp正則性や標数pは仮定しない。
-/

section WittTwoUnits

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- W₂の単元は第0座標と第1ghost成分が単元であることと同値。 -/
theorem wittTwo_isUnit_iff (x : WittTwo p A) :
    IsUnit x ↔ IsUnit (x.coeff 0) ∧ IsUnit (wittTwoFrobenius p A x) := by
  constructor
  · intro hx
    exact ⟨by simpa using hx.map (wittTwoProjection p A), hx.map (wittTwoFrobenius p A)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let y : WittTwo p A := TruncatedWittVector.mk p (fun i ↦
      if i = 0 then (↑a⁻¹ : A) else -x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A))
    have hxy : x * y = 1 := by
      apply TruncatedWittVector.ext
      intro i
      fin_cases i
      · change (x.out * y.out).coeff 0 = (1 : WittVector p A).coeff 0
        rw [WittVector.mul_coeff_zero, WittVector.one_coeff_zero]
        change x.coeff 0 * (↑a⁻¹ : A) = 1
        rw [← ha, Units.mul_inv]
      · change (x.out * y.out).coeff 1 = (1 : WittVector p A).coeff 1
        rw [witt_mul_coeff_one, WittVector.one_coeff_eq_of_pos p A 1 (by decide)]
        change x.coeff 0 ^ p * (-x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A)) +
          x.coeff 1 * (↑a⁻¹ : A) ^ p +
          (p : A) * x.coeff 1 * (-x.coeff 1 * (↑a⁻¹ : A) ^ p * (↑b⁻¹ : A)) = 0
        have hghost : x.coeff 0 ^ p + (p : A) * x.coeff 1 = (b : A) :=
          (wittTwoFrobenius_apply p A x).symm.trans hb.symm
        calc
          _ = x.coeff 1 * (↑a⁻¹ : A) ^ p *
            (1 - (x.coeff 0 ^ p + (p : A) * x.coeff 1) * (↑b⁻¹ : A)) := by ring
          _ = 0 := by rw [hghost, Units.mul_inv]; ring
    exact ⟨⟨x, y, hxy, by simpa [mul_comm] using hxy⟩, rfl⟩

end SerrePositivity.BhattScholze

end WittTwoUnits

/-! ## δの恒等式とW₂切断の対応

BS 著者版 Definition 2.1の恒等式を満たす写像からBS 著者版 Remark 2.4の切断を構成する。
加法補正項は共通Witt APIの整数係数多項式として扱い、pの正則性を要求しない。
-/

section DeltaIdentities

namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δの零・単位・加法・積の恒等式からW₂切断を構成する（BS 著者版 Definition 2.1 の恒等式からの構成）。
座標ごとに環準同型則を確認する（BS 著者版 Definition 2.1とBS 著者版 Remark 2.4の逆向き）。 -/
def ofFunction (δ : A → A) (h0 : δ 0 = 0) (h1 : δ 1 = 0)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    (hmul : ∀ x y, δ (x * y) = x ^ p * δ y + δ x * y ^ p + (p : A) * δ x * δ y) :
    DeltaStructure p A := by
  let s : A → WittTwo p A := fun x ↦ TruncatedWittVector.mk p
    (fun i ↦ if i = 0 then x else δ x)
  refine ⟨{ toFun := s
            map_zero' := ?_
            map_one' := ?_
            map_add' := ?_
            map_mul' := ?_ }, ?_⟩
  · apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change (1 : A) = (1 : WittVector p A).coeff 0
      simp
    · change δ 1 = (1 : WittVector p A).coeff 1
      rw [h1, WittVector.one_coeff_eq_of_pos p A 1 (by decide)]
  · intro x y
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change x * y = ((s x).out * (s y).out).coeff 0
      rw [WittVector.mul_coeff_zero]
      simp [s, TruncatedWittVector.out]
    · change δ (x * y) = ((s x).out * (s y).out).coeff 1
      rw [witt_mul_coeff_one]
      simpa [s, TruncatedWittVector.out] using hmul x y
  · apply TruncatedWittVector.ext
    intro i
    fin_cases i <;> simp [s, h0]
  · intro x y
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change x + y = ((s x).out + (s y).out).coeff 0
      rw [WittVector.add_coeff_zero]
      simp [s, TruncatedWittVector.out]
    · change δ (x + y) = ((s x).out + (s y).out).coeff 1
      rw [witt_add_coeff_one]
      simpa [s, TruncatedWittVector.out] using hadd x y
  · intro x
    rfl

/-- 恒等式から構成したδ構造のδ写像は、与えられた写像そのものである。 -/
@[simp] theorem ofFunction_delta (δ : A → A) (h0 : δ 0 = 0) (h1 : δ 1 = 0)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    (hmul : ∀ x y, δ (x * y) = x ^ p * δ y + δ x * y ^ p + (p : A) * δ x * δ y)
    (x : A) : (ofFunction δ h0 h1 hadd hmul).delta x = δ x := rfl

/-- δ構造から恒等式を取り出して切断を再構成すると、元の構造に戻る。 -/
@[simp] theorem ofFunction_deltaStructure (D : DeltaStructure p A) :
    ofFunction D.delta D.delta_zero D.delta_one D.delta_add D.delta_mul = D := by
  apply ext
  intro x
  rfl

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaIdentities

/-! ## δ射とW₂切断の自然性

δ射の条件をW₂切断の可換図式として表す。自由δ環からの写像を
多項式環の普遍性で構成する際、pねじれのある終域も扱う。
-/

section DeltaSectionNaturality

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環準同型がδ射であることと、W₂切断の図式が可換であることは同値。
二つのWitt座標で比較し、p正則性は要求しない。 -/
theorem isDeltaHom_iff_sectionHom_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) : D.IsDeltaHom E f ↔
      (wittTwoMap (p := p) f).comp D.sectionHom = E.sectionHom.comp f := by
  constructor
  · intro hf
    apply RingHom.ext
    intro x
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      change f ((D.sectionHom x).coeff 0) = (E.sectionHom (f x)).coeff 0
      rw [D.coeff_zero, E.coeff_zero]
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hf x
  · intro h x
    have hx := congrArg (fun z : WittTwo p B ↦ z.coeff 1) (DFunLike.congr_fun h x)
    simp only [RingHom.comp_apply, wittTwoMap_coeff] at hx
    exact hx

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaSectionNaturality

/-! ## p正則な環のFrobenius持上げとδ構造

BS 著者版 Remark 2.2。mod pでFrobeniusと一致する環自己準同型から
δ構造を構成し、一意性を証明する。pねじれのある環への逆向きは主張しない。
-/

section DeltaFrobenius

namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則な環では、φ(x)-x^pがpで割り切れる自己準同型φは一意なδ構造を定める（BS 著者版 Remark 2.2 の p 正則環での逆構成）。
p倍の消去でδの恒等式を証明し、W₂切断を再構成する。 -/
theorem existsUnique_of_frobeniusLift
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) :
    ∃! D : DeltaStructure p A, D.frobeniusLift = φ := by
  let δ : A → A := fun x ↦ Classical.choose (hφ x)
  have hδ (x : A) : φ x = x ^ p + (p : A) * δ x := by
    have h := Classical.choose_spec (hφ x)
    change φ x - x ^ p = (p : A) * δ x at h
    linear_combination h
  have h0 : δ 0 = 0 := by
    apply hp
    have h := hδ 0
    simpa only [map_zero, zero_pow (Fact.out : p.Prime).ne_zero, zero_add, mul_zero]
      using h.symm
  have h1 : δ 1 = 0 := by
    apply hp
    have h := hδ 1
    simp only [map_one, one_pow] at h
    linear_combination -h
  have hadd (x y : A) : δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
    apply hp
    have h := φ.map_add x y
    rw [hδ (x + y), hδ x, hδ y] at h
    have hc := (WittVector.ghostComponent 1).map_add
      (WittVector.teichmuller p x) (WittVector.teichmuller p y)
    simp only [witt_ghostComponent_one, WittVector.add_coeff_zero,
      WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), mul_zero, zero_add] at hc
    linear_combination h - hc
  have hmul (x y : A) : δ (x * y) = x ^ p * δ y + δ x * y ^ p +
      (p : A) * δ x * δ y := by
    apply hp
    have h := φ.map_mul x y
    rw [hδ (x * y), hδ x, hδ y, mul_pow] at h
    linear_combination h
  let D := ofFunction δ h0 h1 hadd hmul
  have hD : D.frobeniusLift = φ := by
    ext x
    exact (D.frobeniusLift_apply x).trans (hδ x).symm
  exact ⟨D, hD, fun E hE ↦ eq_of_frobeniusLift_eq hp (hE.trans hD.symm)⟩

/-- mod pでFrobeniusとなる自己準同型は、p正則な環に一意なδ構造を与える（BS 著者版 Remark 2.2 の p 正則環での逆構成）。
商上の一致をpによる可除性へ移し、存在定理を適用する。 -/
theorem existsUnique_of_mod_p
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (φ : A →+* A)
    (hφ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : A)}) (φ x) =
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) x) ^ p) :
    ∃! D : DeltaStructure p A, D.frobeniusLift = φ := by
  apply existsUnique_of_frobeniusLift hp φ
  intro x
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_pow, hφ x, sub_self]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaFrobenius

/-! ## 環同型によるδ構造の移送

W₂切断を環同型で共役し、元の環構造を変えずにδ構造を引き戻す。
-/

section DeltaTransport

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環同型の終域のδ構造を、W₂切断の共役によって始域へ引き戻す。 -/
def comapEquiv (E : DeltaStructure p B) (e : A ≃+* B) : DeltaStructure p A where
  sectionHom := (wittTwoMap e.symm.toRingHom).comp (E.sectionHom.comp e.toRingHom)
  coeff_zero := by
    intro x
    simp only [RingHom.comp_apply, wittTwoMap_coeff, E.coeff_zero]
    exact e.symm_apply_apply x

/-- 引き戻したδ写像は、環同型を通じた元のδ写像の共役。 -/
@[simp] theorem comapEquiv_delta (E : DeltaStructure p B) (e : A ≃+* B) (x : A) :
    (E.comapEquiv e).delta x = e.symm (E.delta (e x)) := by
  exact wittTwoMap_coeff e.symm.toRingHom (E.sectionHom (e x)) 1

/-- δ構造を引き戻す環同型はδ射。 -/
theorem comapEquiv_isDeltaHom (E : DeltaStructure p B) (e : A ≃+* B) :
    (E.comapEquiv e).IsDeltaHom E e.toRingHom := by
  intro x
  change e ((E.comapEquiv e).delta x) = E.delta (e x)
  rw [comapEquiv_delta]
  exact e.apply_symm_apply _

/-- 同じ環同型の逆も、引き戻したδ構造を保つ。 -/
theorem comapEquiv_symm_isDeltaHom (E : DeltaStructure p B) (e : A ≃+* B) :
    E.IsDeltaHom (E.comapEquiv e) e.symm.toRingHom :=
  (E.comapEquiv_isDeltaHom e).symm

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaTransport

/-! ## δ安定部分環へのδ構造の制限

既存ofFunctionとWittベクトルの自然性を用いる。
-/

section DeltaSubring

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ安定部分環には、元のδ作用を制限したδ構造が入る。 -/
def subring (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) : DeltaStructure p S := by
  let δ : S → S := fun x ↦ ⟨D.delta x, hS x x.property⟩
  apply ofFunction δ
  · exact Subtype.ext D.delta_zero
  · exact Subtype.ext D.delta_one
  · intro x y
    apply Subtype.ext
    have hc : S.subtype ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) =
        (WittVector.teichmuller p (x : A) + WittVector.teichmuller p (y : A)).coeff 1 := by
      rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
        WittVector.map_teichmuller]
      rfl
    change D.delta ((x : A) + (y : A)) = D.delta x + D.delta y +
      S.subtype ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    rw [hc, D.delta_add]
  · intro x y
    apply Subtype.ext
    change D.delta ((x : A) * (y : A)) =
      (x : A) ^ p * D.delta y + D.delta x * (y : A) ^ p + (p : A) * D.delta x * D.delta y
    exact D.delta_mul x y

/-- 制限したδ作用は、元のδ作用の部分型への制限そのもの。 -/
theorem subring_delta (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) (x : S) :
    (D.subring S hS).delta x = ⟨D.delta x, hS x x.property⟩ := rfl

/-- δ安定部分環の包含はδ射。 -/
theorem subring_subtype_isDeltaHom (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) : (D.subring S hS).IsDeltaHom D S.subtype := by
  intro x
  rfl

/-- 包含をδ射にする部分環のδ構造は、制限したδ構造と一意に一致する。 -/
theorem subring_unique (D : DeltaStructure p A) (S : Subring A)
    (hS : ∀ x ∈ S, D.delta x ∈ S) (E : DeltaStructure p S)
    (hE : E.IsDeltaHom D S.subtype) : E = D.subring S hS := by
  apply DeltaStructure.ext
  intro x
  apply Subtype.ext
  exact hE x

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaSubring

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 2.1"] _root_.SerrePositivity.BhattScholze.DeltaStructure
attribute [cite BS19 "Def 2.1"] _root_.SerrePositivity.BhattScholze.DeltaStructure.delta_add
attribute [cite BS19 "Def 2.1"] _root_.SerrePositivity.BhattScholze.DeltaStructure.delta_mul
attribute [cite BS19 "Def 2.1"] _root_.SerrePositivity.BhattScholze.DeltaStructure.ofFunction
attribute [cite BS19 "Def 2.19"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDeltaHom.map_isDistinguished
attribute [cite BS19 "Def 2.19"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished
attribute [cite BS19 "Def 2.26"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsPerfect
attribute [cite BS19 "Rem 1.2"] _root_.SerrePositivity.BhattScholze.DeltaStructure
attribute [cite BS19 "Rem 1.2"] _root_.SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift
attribute [cite BS19 "Rem 2.2"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_frobeniusLift
attribute [cite BS19 "Rem 2.2"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_mod_p
attribute [cite BS19 "Rem 2.2"] _root_.SerrePositivity.BhattScholze.DeltaStructure.frobeniusLift
attribute [cite BS19 "Rem 2.4"] _root_.SerrePositivity.BhattScholze.DeltaStructure
attribute [cite BS19 "Rem 2.4"] _root_.SerrePositivity.BhattScholze.WittTwo
