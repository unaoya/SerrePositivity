module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# δ とイデアル冪の評価と、古典的 I 進完備化への延長（BS 著者版 Lemma 2.17）

## 概要
環射に沿う W₂ 持ち上げの相対 δ の公式とイデアル冪の評価、p ∈ I なら δ(I^{n+1}) ⊂ Iⁿ、
δ の有限 I 進商への降下、古典的 I 進完備化の δ 構造（一意性は I 有限生成）と、完備化からの δ 射の延長。

## 方針
評価から δ を Cauchy 列に座標ごとに作用させる。原典の I^{2^{n+1}} → I^{2^n} より強い m = n+1 の評価を使う。

## 規約
存在に有限生成性・p 正則性は不要。導来完備化との比較はここにはない。

## 使われ方
BS 著者版 Corollary 7.3 の構成、完全化の p 進完備化、相対自由 δ 環の有限段の計算。
-/

@[expose] public noncomputable section
universe u v w

/-! ## δ とイデアル冪の評価（BS 著者版 Lemma 2.17 の連続性）

## 概要
環射 f を第 0 座標とする W₂ への持ち上げの第 1 座標（相対 δ）の加法・乗法公式とイデアル冪の評価、
その特別な場合として p ∈ I なら δ(I^{n+1}) ⊂ Iⁿ。

## 方針
加法公式の補正項がイデアルに入ることと積公式から、冪の指数を一つずつ落とす。

## 規約
有限生成性・p 正則性・完備性は不要。

## 使われ方
古典的 I 進完備化への延長（Extension/DeltaAdicCompletion）、相対自由 δ 環の有限段の計算（Free/Finite）。
-/

section DeltaAdicEstimate

/-! ## 環射に沿うW₂持上げの相対δ評価

環射fを第0座標とするW₂持上げsの第1座標を、相対δとして扱う。
通常δ構造や有限段の計算射を再定義せず、イデアル冪評価と通常剰余公式を共有する。
-/

section RelativeDeltaEstimate

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Witt加法繰上りは第2引数を含む任意のイデアルに属する。
商へのWitt射を使い、pを約分しない。 -/
theorem wittAdditionCarry_mem_of_right_mem (I : Ideal R) (x y : R) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  simp

variable {S : Type v} [CommRing S]
variable (f : R →+* S) (s : R →+* WittTwo p S)
variable (hs : (wittTwoProjection p S).comp s = f)
local notation "δ" => fun x ↦ TruncatedWittVector.coeff (1 : Fin 2) (s x)
include hs

/-- 相対W₂持上げの第0座標は指定した環射。 -/
theorem wittTwoLift_coeff_zero (x : R) : (s x).coeff 0 = f x :=
  (wittTwoProjection_apply p S (s x)).symm.trans (RingHom.congr_fun hs x)

/-- 相対δの加法公式。補正項の二入力は指定した環射の像。 -/
theorem wittTwoLift_delta_add (x y : R) :
    δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p (f x) + WittVector.teichmuller p (f y)).coeff 1 := by
  change (s (x + y)).coeff 1 = _
  rw [map_add]
  change ((s x).out + (s y).out).coeff 1 = _
  rw [witt_add_coeff_one]
  simp [TruncatedWittVector.out, wittTwoLift_coeff_zero f s hs]

/-- 相対δの積公式。終域でのp正則性を要求しない。 -/
theorem wittTwoLift_delta_mul (x y : R) :
    δ (x * y) = f x ^ p * δ y + δ x * f y ^ p + (p : S) * δ x * δ y := by
  change (s (x * y)).coeff 1 = _
  rw [map_mul]
  change ((s x).out * (s y).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, wittTwoLift_coeff_zero f s hs]

/-- pを含む終域イデアルの逆像のn+1乗は、相対δでそのイデアルのn乗に入る。
仮定は逆像イデアルの冪であり、冪イデアルへの像の所属ではない。 -/
theorem wittTwoLift_delta_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x : R) (hx : x ∈ (J.comap f) ^ (n + 1)) : δ x ∈ J ^ n := by
  let I := J.comap f
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hmul : x ∈ (I ^ (n + 1)) * I := by simpa only [I, pow_succ] using hx
    have he : f x ∈ J ^ (n + 1) ∧ δ x ∈ J ^ (n + 1) := by
      refine Submodule.mul_induction_on (C := fun z ↦
        f z ∈ J ^ (n + 1) ∧ δ z ∈ J ^ (n + 1)) hmul ?_ ?_
      · intro a ha b hb
        have ha' : f a ∈ J ^ (n + 1) := Ideal.le_comap_pow f (n + 1) ha
        have hb' : f b ∈ J := hb
        constructor
        · rw [map_mul]
          exact (J ^ (n + 1)).mul_mem_right _ ha'
        · rw [wittTwoLift_delta_mul f s hs]
          apply (J ^ (n + 1)).add_mem
          · apply (J ^ (n + 1)).add_mem
            · exact (J ^ (n + 1)).mul_mem_right _
                ((J ^ (n + 1)).pow_mem_of_mem ha' p (Fact.out : p.Prime).pos)
            · have hprod := Ideal.mul_mem_mul (ih a ha)
                (J.pow_mem_of_mem hb' p (Fact.out : p.Prime).pos)
              simpa only [pow_succ] using hprod
          · have hprod := Ideal.mul_mem_mul (ih a ha) hp
            have hprod' : δ a * (p : S) ∈ J ^ (n + 1) := by
              simpa only [pow_succ] using hprod
            simpa only [mul_comm, mul_left_comm, mul_assoc] using
              (J ^ (n + 1)).mul_mem_right (δ b) hprod'
      · intro a b ha hb
        constructor
        · rw [map_add]
          exact (J ^ (n + 1)).add_mem ha.1 hb.1
        · rw [wittTwoLift_delta_add f s hs]
          exact (J ^ (n + 1)).add_mem ((J ^ (n + 1)).add_mem ha.2 hb.2)
            (wittAdditionCarry_mem_of_right_mem (J ^ (n + 1)) _ _ hb.1)
    exact he.2

/-- 逆像イデアルのn+1乗の摂動による相対δの変化は、終域イデアルのn乗に入る。 -/
theorem wittTwoLift_delta_add_sub_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x y : R) (hy : y ∈ (J.comap f) ^ (n + 1)) : δ (x + y) - δ x ∈ J ^ n := by
  have hy' : f y ∈ J ^ (n + 1) := Ideal.le_comap_pow f (n + 1) hy
  have hc := wittAdditionCarry_mem_of_right_mem (p := p) (J ^ (n + 1)) (f x) (f y) hy'
  have he := (J ^ n).add_mem (wittTwoLift_delta_mem_pow f s hs J hp n y hy)
    (Ideal.pow_le_pow_right (by omega : n ≤ n + 1) hc)
  rw [wittTwoLift_delta_add f s hs]
  convert he using 1
  ring

/-- 二入力が逆像イデアルのn+1乗まで一致すれば、相対δは終域イデアルのn乗まで一致。 -/
theorem wittTwoLift_delta_sub_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x y : R) (hxy : x - y ∈ (J.comap f) ^ (n + 1)) : δ x - δ y ∈ J ^ n := by
  have he := wittTwoLift_delta_add_sub_mem_pow f s hs J hp n y (x - y) hxy
  simpa only [add_sub_cancel] using he

variable {T : Type w} [CommRing T]

/-- 左入力の像を消す通常環射の下で、相対δの加法補正項は消える。 -/
theorem wittTwoLift_map_delta_add_of_left_zero (q : S →+* T)
    (x y : R) (hx : q (f x) = 0) : q (δ (x + y)) = q (δ x) + q (δ y) := by
  rw [wittTwoLift_delta_add f s hs, map_add, map_add]
  have hc : q ((WittVector.teichmuller p (f x) +
      WittVector.teichmuller p (f y)).coeff 1) = 0 := by
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hx, WittVector.teichmuller_zero, zero_add]
    exact WittVector.teichmuller_coeff_pos p (q (f y)) 1 (by decide)
  rw [hc, add_zero]

/-- 右入力の像を消す通常環射の下での相対δ加法公式。 -/
theorem wittTwoLift_map_delta_add_of_right_zero (q : S →+* T)
    (x y : R) (hy : q (f y) = 0) : q (δ (x + y)) = q (δ x) + q (δ y) := by
  rw [add_comm x y, wittTwoLift_map_delta_add_of_left_zero f s hs q y x hy, add_comm]

/-- pを消す通常環射の下での相対δ積公式。 -/
theorem wittTwoLift_map_delta_mul_of_prime_zero (q : S →+* T)
    (hp : q (p : S) = 0) (x y : R) :
    q (δ (x * y)) = (q (f x)) ^ p * q (δ y) + q (δ x) * (q (f y)) ^ p := by
  rw [wittTwoLift_delta_mul f s hs, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
    map_pow, map_pow, hp, zero_mul, zero_mul, add_zero]

end SerrePositivity.BhattScholze

end RelativeDeltaEstimate

/-! ## δ写像のイデアル冪に対する評価

BS 著者版 Lemma 2.17の連続性に使う代数的評価。
p∈Iならδ(I^{n+1})⊂I^nを証明する。有限生成性・p正則性・完備性は不要。
完備化へのδ構造の延長はここでは構成しない。
-/

section DeltaAdicEstimate

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

namespace DeltaStructure

/-- pを含むイデアルのn+1乗の元のδは、そのn乗に属する（BS 著者版 Lemma 2.17 の連続性に使うイデアル冪の評価）。 -/
theorem delta_mem_pow (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (n : ℕ) (x : R) (hx : x ∈ I ^ (n + 1)) : D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x
    (by simpa only [Ideal.comap_id] using hx)

/-- I^{n+1}の摂動でδの値はI^nの範囲でしか変わらない。
BS 著者版 Lemma 2.17の具体的な連続性評価m=n+1。 -/
theorem delta_add_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hy : y ∈ I ^ (n + 1)) :
    D.delta (x + y) - D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_add_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hy)

/-- x,yがmod I^{n+1}で一致すればδx,δyはmod I^nで一致する。 -/
theorem delta_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ (n + 1)) :
    D.delta x - D.delta y ∈ I ^ n := by
  exact wittTwoLift_delta_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hxy)

end DeltaStructure
end SerrePositivity.BhattScholze

end DeltaAdicEstimate

end DeltaAdicEstimate

/-! ## δの有限I進商への降下

p∈IのもとでδはR/I^{n+1}→R/I^nという集合の写像を定める。
環射や各R/I^nのδ構造ではない。完備化の座標構成に使う。
-/

section DeltaAdicQuotient

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- δを一段深い商から浅い商へ降下させた写像。 -/
def adicDeltaStep (D : DeltaStructure p R) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ (n + 1) → R ⧸ I ^ n :=
  fun x ↦ Ideal.Quotient.mk (I ^ n) (D.delta (Quotient.out x))

/-- p∈Iなら降下写像は代表元のδを取る写像である。 -/
@[simp] theorem adicDeltaStep_mk (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x : R) :
    D.adicDeltaStep I n (Ideal.Quotient.mk (I ^ (n + 1)) x) =
      Ideal.Quotient.mk (I ^ n) (D.delta x) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply D.delta_sub_mem_pow I hp n
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (Ideal.Quotient.mk_out _)

/-- δの一段ずらした写像はI進商の標準遷移と可換。 -/
theorem adicDeltaStep_factorPow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ (n + 1)) :
    Ideal.Quotient.factorPow I hmn (D.adicDeltaStep I n x) =
      D.adicDeltaStep I m (Ideal.Quotient.factorPow I (Nat.add_le_add_right hmn 1) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [D.adicDeltaStep_mk I hp]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaAdicQuotient

/-! ## 古典的I進完備化上のδ写像の座標構成

MathlibのCauchy列・古典的完備化を使い、一段ずらしたδ列から写像を構成する。
導来完備化との比較はこのモジュールの対象外。
-/

section DeltaAdicExtension

namespace SerrePositivity.BhattScholze.DeltaStructure
open AdicCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 一段ずらしたδ列は再びI進Cauchy列。 -/
def adicDeltaSequence (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (f : AdicCauchySequence I R) : AdicCauchySequence I R :=
  ⟨fun n ↦ D.delta (f (n + 1)), by
    intro m n hmn
    apply SModEq.sub_mem.mpr
    have h := (f.property (Nat.add_le_add_right hmn 1))
    have h' : f (m + 1) - f (n + 1) ∈ I ^ (m + 1) := by
      simpa [SModEq.sub_mem, smul_eq_mul] using h
    simpa [smul_eq_mul] using D.delta_sub_mem_pow I hp m _ _ h'⟩

/-- 古典的完備化の元を表すCauchy列にδを作用させる。
以下の座標式により選択した代表列によらない。 -/
def adicDeltaExtension (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (x : AdicCompletion I R) : AdicCompletion I R :=
  AdicCompletion.mk I R
    (D.adicDeltaSequence I hp (Classical.choose (AdicCompletion.mk_surjective I R x)))

/-- 延長写像のn番目の座標は、元のn+1番目の座標に降下δを適用したもの。 -/
theorem eval_adicDeltaExtension (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (D.adicDeltaExtension I hp x) =
      D.adicDeltaStep I n (AdicCompletion.evalₐ I (n + 1) x) := by
  let f := Classical.choose (AdicCompletion.mk_surjective I R x)
  have hf : AdicCompletion.mk I R f = x :=
    Classical.choose_spec (AdicCompletion.mk_surjective I R x)
  change AdicCompletion.evalₐ I n (AdicCompletion.mk I R (D.adicDeltaSequence I hp f)) = _
  rw [AdicCompletion.evalₐ_mk, ← hf, AdicCompletion.evalₐ_mk, D.adicDeltaStep_mk I hp]
  rfl

/-- 基底のδ写像を標準完備化射で延長する。 -/
@[simp] theorem adicDeltaExtension_of (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x : R) :
    D.adicDeltaExtension I hp (AdicCompletion.of I R x) =
      AdicCompletion.of I R (D.delta x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [D.eval_adicDeltaExtension, AdicCompletion.evalₐ_of, D.adicDeltaStep_mk I hp,
    AdicCompletion.evalₐ_of]

/-- 任意の代表Cauchy列についてδ延長の値が一段ずらしたδ列に一致する。
代表列の選択に依存しないことの具体的な証明。 -/
theorem adicDeltaExtension_mk (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (f : AdicCauchySequence I R) :
    D.adicDeltaExtension I hp (AdicCompletion.mk I R f) =
      AdicCompletion.mk I R (D.adicDeltaSequence I hp f) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [D.eval_adicDeltaExtension, AdicCompletion.evalₐ_mk, D.adicDeltaStep_mk I hp,
    AdicCompletion.evalₐ_mk]
  rfl

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaAdicExtension

/-! ## 古典的I進完備化のδ構造

BS 著者版 Lemma 2.17の存在部分。Mathlibの古典的完備化上に構成したδ写像が
δ恒等式を満たすことを有限商の座標で確認する。導来完備化への置換ではない。
-/

section DeltaAdicCompletion

namespace SerrePositivity.BhattScholze.DeltaStructure
open AdicCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

private theorem exists_successor_representative (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) : ∃ r : R,
      evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) r ∧
      evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  refine ⟨f (n + 1), by rw [evalₐ_mk], ?_⟩
  rw [evalₐ_mk]
  simpa [SModEq.def, smul_eq_mul] using f.property (Nat.le_succ n)

/-- 完備化上のδ写像は積公式を満たす。 -/
theorem adicDeltaExtension_mul (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x y : AdicCompletion I R) :
    D.adicDeltaExtension I hp (x * y) =
      x ^ p * D.adicDeltaExtension I hp y + D.adicDeltaExtension I hp x * y ^ p +
        (p : AdicCompletion I R) * D.adicDeltaExtension I hp x * D.adicDeltaExtension I hp y := by
  apply ext_evalₐ
  intro n
  obtain ⟨a, ha, ha'⟩ := exists_successor_representative I n x
  obtain ⟨b, hb, hb'⟩ := exists_successor_representative I n y
  rw [D.eval_adicDeltaExtension, map_mul, ha, hb, ← map_mul,
    D.adicDeltaStep_mk I hp, D.delta_mul]
  simp only [map_add, map_mul, map_pow, map_natCast]
  rw [D.eval_adicDeltaExtension, D.eval_adicDeltaExtension, ha, hb,
    D.adicDeltaStep_mk I hp, D.adicDeltaStep_mk I hp, ha', hb']

/-- 完備化上のδ写像はWitt繰上りを含む加法公式を満たす。 -/
theorem adicDeltaExtension_add (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x y : AdicCompletion I R) :
    D.adicDeltaExtension I hp (x + y) =
      D.adicDeltaExtension I hp x + D.adicDeltaExtension I hp y +
        (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  apply ext_evalₐ
  intro n
  obtain ⟨a, ha, ha'⟩ := exists_successor_representative I n x
  obtain ⟨b, hb, hb'⟩ := exists_successor_representative I n y
  rw [D.eval_adicDeltaExtension, map_add, ha, hb, ← map_add, D.adicDeltaStep_mk I hp,
    D.delta_add]
  simp only [map_add, D.eval_adicDeltaExtension, ha, hb, D.adicDeltaStep_mk I hp]
  congr 1
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller]
  symm
  change (evalₐ I n).toRingHom
    ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) = _
  rw [← WittVector.map_coeff (evalₐ I n).toRingHom, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller]
  change (WittVector.teichmuller p (evalₐ I n x) +
    WittVector.teichmuller p (evalₐ I n y)).coeff 1 = _
  rw [ha', hb']

/-- pを含む任意のイデアルの古典的完備化のδ構造（BS 著者版 Lemma 2.17 の第二文の構成）。
存在の構成に有限生成性・p正則性は不要。 -/
def adicCompletion (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I) :
    DeltaStructure p (AdicCompletion I R) :=
  ofFunction (D.adicDeltaExtension I hp)
    (by have h := D.adicDeltaExtension_of I hp 0
        rw [D.delta_zero, _root_.map_zero] at h
        exact h)
    (by have h := D.adicDeltaExtension_of I hp 1
        rw [D.delta_one, _root_.map_zero] at h
        exact h)
    (D.adicDeltaExtension_add I hp) (D.adicDeltaExtension_mul I hp)

/-- 完備化δ構造のδは構成した座標延長に等しい。 -/
@[simp] theorem adicCompletion_delta (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (x : AdicCompletion I R) :
    (D.adicCompletion I hp).delta x = D.adicDeltaExtension I hp x := rfl

/-- 基底から古典的完備化への標準環射はδ射。 -/
theorem isDeltaHom_adicCompletion (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) :
    D.IsDeltaHom (D.adicCompletion I hp) (algebraMap R (AdicCompletion I R)) := by
  intro x
  exact (D.adicDeltaExtension_of I hp x).symm

/-- Iが有限生成なら、標準射と両立する古典的完備化のδ構造は一意。
共通層の評価核と拡張イデアル冪の一致を使用する。 -/
theorem adicCompletion_unique (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (hI : I.FG) (E : DeltaStructure p (AdicCompletion I R))
    (hE : D.IsDeltaHom E (algebraMap R (AdicCompletion I R))) :
    E = D.adicCompletion I hp := by
  apply ext
  intro x
  apply ext_evalₐ
  intro n
  obtain ⟨r, hr, _⟩ := exists_successor_representative I n x
  let f := algebraMap R (AdicCompletion I R)
  let J := I.map f
  have hpJ : (p : AdicCompletion I R) ∈ J := by
    simpa only [map_natCast] using Ideal.mem_map_of_mem f hp
  have hxJ : x - f r ∈ J ^ (n + 1) := by
    rw [← SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    change evalₐ I (n + 1) (x - f r) = 0
    rw [map_sub, hr]
    change Ideal.Quotient.mk _ r - Ideal.Quotient.mk _ r = 0
    exact sub_self _
  have he := E.delta_sub_mem_pow J hpJ n x (f r) hxJ
  have he' : evalₐ I n (E.delta x - E.delta (f r)) = 0 := by
    change E.delta x - E.delta (f r) ∈ RingHom.ker (evalₐ I n).toRingHom
    rw [SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    exact he
  rw [map_sub, ← hE r] at he'
  rw [adicCompletion_delta, D.eval_adicDeltaExtension, hr, D.adicDeltaStep_mk I hp]
  exact sub_eq_zero.mp he'

/-- pを含む有限生成イデアルの古典的完備化は、一意な適合δ構造を持つ（BS 著者版 Lemma 2.17 の第二文の存在一意性）。
BS 著者版 Lemma 2.17の存在・一意性。 -/
theorem existsUnique_adicCompletion (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (hI : I.FG) :
    ∃! E : DeltaStructure p (AdicCompletion I R),
      D.IsDeltaHom E (algebraMap R (AdicCompletion I R)) :=
  ⟨D.adicCompletion I hp, D.isDeltaHom_adicCompletion I hp,
    fun E hE ↦ D.adicCompletion_unique I hp hI E hE⟩

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaAdicCompletion

/-! ## 古典的完備化からのδ射の延長

有限生成I、p∈I、J進分離したδ終域への基底δ射を扱う。
Mathlibの完備化・環射の持上げと共通評価核APIを再利用する。
導来完備化との比較やBS 著者版 Proposition 7.2の超限構成を代替しない。
-/

section DeltaAdicLift

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A]

/-- 基底δ射を延長する環射は、終域がJ進分離していればδ射。
源の有限生成性とf(I)⊂Jを公開仮定に明示する。 -/
theorem IsDeltaHom.adicCompletion_extension {D : DeltaStructure p R}
    {E : DeltaStructure p A} {f : R →+* A} (hf : D.IsDeltaHom E f)
    (I : Ideal R) (hp : (p : R) ∈ I) (hI : I.FG) (J : Ideal A) [IsHausdorff J A]
    (hIJ : I.map f ≤ J) (g : AdicCompletion I R →+* A)
    (hg : g.comp (algebraMap R (AdicCompletion I R)) = f) :
    (D.adicCompletion I hp).IsDeltaHom E g := by
  let j := algebraMap R (AdicCompletion I R)
  let K := I.map j
  have hK : K.map g ≤ J := by
    change (I.map j).map g ≤ J
    rw [Ideal.map_map, hg]
    exact hIJ
  have hmap (n : ℕ) (z : AdicCompletion I R) (hz : z ∈ K ^ n) : g z ∈ J ^ n := by
    have h := Ideal.mem_map_of_mem g hz
    rw [Ideal.map_pow] at h
    exact Ideal.pow_right_mono hK n h
  have hpK : (p : AdicCompletion I R) ∈ K := by
    simpa only [map_natCast] using Ideal.mem_map_of_mem j hp
  have hpJ : (p : A) ∈ J := by
    simpa only [map_natCast] using hIJ (Ideal.mem_map_of_mem f hp)
  have hgj (r : R) : g (j r) = f r := DFunLike.congr_fun hg r
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  apply SModEq.sub_mem.mpr
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have hx : x - j r ∈ K ^ (n + 1) := by
    rw [← SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    change AdicCompletion.evalₐ I (n + 1) (x - j r) = 0
    rw [map_sub, ← hr]
    change Ideal.Quotient.mk _ r - Ideal.Quotient.mk _ r = 0
    exact sub_self _
  have hl := hmap n _ ((D.adicCompletion I hp).delta_sub_mem_pow K hpK n x (j r) hx)
  rw [map_sub, ← D.isDeltaHom_adicCompletion I hp r, hgj] at hl
  have hx' := hmap (n + 1) _ hx
  rw [map_sub, hgj] at hx'
  have hr' := E.delta_sub_mem_pow J hpJ n (g x) (f r) hx'
  rw [← hf r] at hr'
  have h := (J ^ n).sub_mem hl hr'
  simpa only [sub_sub_sub_cancel_right, smul_eq_mul, Ideal.mul_top] using h

/-- 完備化から分離した終域への基底射の延長は一意。
δ射の公開普遍性に使う、具体的な基底射に相対的な外延性。 -/
theorem adicCompletion_extension_unique (I : Ideal R) (hI : I.FG) (J : Ideal A)
    [IsHausdorff J A] (f : R →+* A) (hIJ : I.map f ≤ J)
    (g k : AdicCompletion I R →+* A)
    (hg : g.comp (algebraMap R (AdicCompletion I R)) = f)
    (hk : k.comp (algebraMap R (AdicCompletion I R)) = f) : g = k := by
  let := f.toAlgebra
  let : IsHausdorff I A := IsHausdorff.of_map hIJ
  let ga : AdicCompletion I R →ₐ[R] A :=
    { g with commutes' := fun r ↦ DFunLike.congr_fun hg r }
  let ka : AdicCompletion I R →ₐ[R] A :=
    { k with commutes' := fun r ↦ DFunLike.congr_fun hk r }
  have he : ga.toLinearMap = ka.toLinearMap :=
    SerrePositivity.adicCompletion_linearMap_ext_of_of I hI _ _ (by
      apply LinearMap.ext
      intro r
      exact (DFunLike.congr_fun hg r).trans (DFunLike.congr_fun hk r).symm)
  ext x
  exact DFunLike.congr_fun he x

/-- pを含む有限生成Iの古典的完備化から、J進完備δ環への一意な延長。
具体的な基底δ射fとf(I)⊂Jを仮定する。 -/
theorem existsUnique_adicCompletion_lift (D : DeltaStructure p R) (E : DeltaStructure p A)
    (I : Ideal R) (hp : (p : R) ∈ I) (hI : I.FG) (J : Ideal A) [IsAdicComplete J A]
    (f : R →+* A) (hf : D.IsDeltaHom E f) (hIJ : I.map f ≤ J) :
    ∃! g : AdicCompletion I R →+* A,
      g.comp (algebraMap R (AdicCompletion I R)) = f ∧
        (D.adicCompletion I hp).IsDeltaHom E g := by
  let q (n : ℕ) : R ⧸ I ^ n →+* A ⧸ J ^ n :=
    Ideal.Quotient.lift (I ^ n) ((Ideal.Quotient.mk (J ^ n)).comp f) (by
      intro r hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have h := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h
      exact Ideal.pow_right_mono hIJ n h)
  let F (n : ℕ) : AdicCompletion I R →+* A ⧸ J ^ n :=
    (q n).comp (AdicCompletion.evalₐ I n).toRingHom
  have hF {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow J hmn).comp (F n) = F m := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
    simp only [F, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, q]
    change Ideal.Quotient.mk (J ^ m) (f (a n)) = Ideal.Quotient.mk (J ^ m) (f (a m))
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have ha : a n - a m ∈ I ^ m := by
      simpa [SModEq.sub_mem, smul_eq_mul] using (a.property hmn).symm
    have h := Ideal.mem_map_of_mem f ha
    rw [Ideal.map_pow, map_sub] at h
    exact Ideal.pow_right_mono hIJ m h
  let g := IsAdicComplete.liftRingHom J F (fun h ↦ hF h)
  have hg : g.comp (algebraMap R (AdicCompletion I R)) = f := by
    apply RingHom.ext
    intro r
    apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    change Ideal.Quotient.mk (J ^ n) (g (algebraMap R (AdicCompletion I R) r)) =
      Ideal.Quotient.mk (J ^ n) (f r)
    rw [IsAdicComplete.mk_liftRingHom]
    change q n (AdicCompletion.evalₐ I n (AdicCompletion.of I R r)) = _
    rw [AdicCompletion.evalₐ_of]
    rfl
  refine ⟨g, ⟨hg, hf.adicCompletion_extension I hp hI J hIJ g hg⟩, ?_⟩
  intro k hk
  exact adicCompletion_extension_unique I hI J f hIJ k g hk.1 hg

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaAdicLift

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.17"] _root_.SerrePositivity.BhattScholze.DeltaStructure.adicCompletion
attribute [cite BS19 "Lemma 2.17"] _root_.SerrePositivity.BhattScholze.DeltaStructure.delta_mem_pow
attribute [cite BS19 "Lemma 2.17"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_adicCompletion
