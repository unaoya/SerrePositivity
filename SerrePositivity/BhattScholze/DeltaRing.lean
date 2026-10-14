module

public import Mathlib.RingTheory.WittVector.Truncated
public import SerrePositivity.CommutativeAlgebra.WittCoefficientOne
public import SerrePositivity.CommutativeAlgebra.WittAdditionCarry
public import Mathlib.Tactic.FinCases

/-! # δ環のW₂切断による表現

BS著者公開版Remark 2.4の切断を採用する。pねじれの消去を仮定せず、
MathlibのWitt環を使ってδ構造とFrobenius持上げを表す。
-/

@[expose] public noncomputable section

universe u v w
namespace SerrePositivity.BhattScholze

variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]

/-- 長さ2のWitt環。δ構造を表す切断の行先として用いる。 -/
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

/-- δ構造はW₂の第0成分射の環準同型切断（BS著者版Remark 2.4）。
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

/-- δの積公式（BS著者版Def 2.1）。既存のWitt第1積係数公式を適用し、
pねじれの消去を使わずに証明する。 -/
theorem delta_mul (D : DeltaStructure p A) (x y : A) :
    D.delta (x * y) = x ^ p * D.delta y + D.delta x * y ^ p +
      (p : A) * D.delta x * D.delta y := by
  change (D.sectionHom (x * y)).coeff 1 = _
  rw [map_mul]
  change ((D.sectionHom x).out * (D.sectionHom y).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, D.coeff_zero, delta]

/-- δの加法公式（BS著者版Def 2.1）。共通Witt加法係数を再利用し、
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

/-- δ構造のFrobenius持上げ。第1ghost成分と切断を合成する（BS Remark 2.2）。 -/
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

/-- distinguished元はδ(d)が単元である元（BS著者版Definition 2.19）。 -/
def IsDistinguished (D : DeltaStructure p A) (d : A) : Prop := IsUnit (D.delta d)

/-- 完全δ構造はFrobenius持上げが全単射である構造。完全prismの条件に用いる。 -/
def IsPerfect (D : DeltaStructure p A) : Prop := Function.Bijective D.frobeniusLift

/-- 環準同型がδと可換であるという条件。pねじれを持つ環でもδの情報を保持する。 -/
def IsDeltaHom {B : Type v} [CommRing B] (D : DeltaStructure p A)
    (E : DeltaStructure p B) (f : A →+* B) : Prop := ∀ x, f (D.delta x) = E.delta (f x)

/-- δと可換な環準同型はFrobenius持上げとも可換。座標式と準同型則で証明する。 -/
theorem IsDeltaHom.map_frobeniusLift {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) (x : A) : f (D.frobeniusLift x) = E.frobeniusLift (f x) := by
  simp only [frobeniusLift_apply, map_add, map_mul, map_pow, map_natCast, hf x]

/-- δ射はdistinguished元を保存する。δの可換性と単元の像を使う（BS Def 2.19）。 -/
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

/-- pを零に送る任意の環準同型上で、φはp乗と一致する。
特にA/(p)上のFrobeniusを持ち上げるというBS Remark 2.2の主張を与える。 -/
theorem map_frobeniusLift_of_map_p_eq_zero {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (f : A →+* B) (hp : f (p : A) = 0) (x : A) :
    f (D.frobeniusLift x) = f x ^ p := by
  rw [frobeniusLift_apply, map_add, map_mul, map_pow, hp, zero_mul, add_zero]

/-- p正則な環では、Frobenius持上げが一致するδ構造は一致する。
p倍を消去してδを復元し、切断の座標による外延性を使う（BS Remark 2.2の一意性）。 -/
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

/-- δで安定なイデアル。商δ環とδ閉包の構成（BS Lemma 2.9）の入力に使う。 -/
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
