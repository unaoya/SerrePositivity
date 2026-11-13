module
public import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Identity

public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectPrismMonic
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection

/-!
# ω₁ 塔と André の平坦性補題（BS 著者版 Theorem 7.14）

## 概要
固定初段上の塔の代数の圏と実余極限、族の一元飽和と拡大、一元拡大（`Perfection/PerfectPrismMonic`）の任意の perfectoid 基底への移送、ω₁ 反復の存在と終段の三性質、BS 著者版 Theorem 7.14 の無条件存在定理 `exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、一般の有向系の完備化。
一元のモニック方程式に根を足す完全忠実平坦拡大を後続段に使い、BS 著者版 Theorem 7.14 の絶対整閉拡大を作る。Remark 7.15 の mod p ind-syntomic 性はこの構成の結論に含めない。

## 方針
原典は R ↦ R₁ を超限回くり返すとだけ書く。Lean では後続基数による一元ずつの飽和と `SmallObject.SuccStruct.iterationFunctor` で ω₁ まで反復し、終段は可算個の証人の降下で自動的に p 進完備になる。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
AndreFlatness、BS の集約。
-/

universe u v

/-! ## AlgebraColimit -/

@[expose] public noncomputable section AlgebraColimit

open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
local notation "L" => Ring.DirectLimit S (fun i j h ↦ AlgHom.toRingHom (f i j h))
local notation "D" => _root_.DirectLimit S f
local notation "ofL" => Ring.DirectLimit.of S (fun i j h ↦ AlgHom.toRingHom (f i j h))
/-- ## 概要
環余極限モデルと代数の非交和余極限モデルの環同型を作る。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
両モデルの普遍性から二つの環写像を作り、標準段射上で両合成を検証する。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitEquiv : L ≃+* D := by
  let a : L →+* D := Ring.DirectLimit.lift S (fun i j h ↦ AlgHom.toRingHom (f i j h)) D
    (_root_.DirectLimit.Ring.of S f) (fun i j h x ↦ _root_.DirectLimit.Ring.of_f h x)
  let b : D →+* L := _root_.DirectLimit.Ring.lift S f L ofL
    (fun i j h x ↦ Ring.DirectLimit.of_f h x)
  have hba : b.comp a = RingHom.id L := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change b (a (ofL i x)) = _
    have ha : a (ofL i x) = _root_.DirectLimit.Ring.of S f i x := Ring.DirectLimit.lift_of ..
    rw [ha]
    rfl
  have hab : a.comp b = RingHom.id D := by
    apply _root_.DirectLimit.Ring.hom_ext
    intro i
    ext x
    change a (ofL i x) = _
    exact Ring.DirectLimit.lift_of ..
  exact
    { a with
      invFun := b
      left_inv := RingHom.congr_fun hba
      right_inv := RingHom.congr_fun hab }
/-- ## 概要
余極限モデルの比較同型は各標準段射を保つ。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
実際の環余極限の持上げの計算規則を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitEquiv_of (i : ι) (x : S i) :
    algebraRingDirectLimitEquiv S f (ofL i x) = _root_.DirectLimit.Ring.of S f i x := by
  exact Ring.DirectLimit.lift_of
    (f := fun i j h ↦ AlgHom.toRingHom (f i j h)) D (_root_.DirectLimit.Ring.of S f)
    (fun i j h x ↦ _root_.DirectLimit.Ring.of_f (G := S) (f := f) h x) i x
/-- ## 概要
代数有向系の環余極限への共通基底の標準写像を定める。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
非交和代数余極限の係数写像を、明示的な比較同型の逆写像で移す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitBaseMap : A →+* L :=
  (algebraRingDirectLimitEquiv S f).symm.toRingHom.comp (algebraMap A D)
/-- ## 概要
共通基底の余極限への標準写像は、任意の一段を経由する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
比較同型の単射性と、非交和余極限の係数写像の任意の段での表示を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitBaseMap_eq (i : ι) (a : A) :
    algebraRingDirectLimitBaseMap S f a = ofL i (algebraMap A (S i) a) := by
  apply (algebraRingDirectLimitEquiv S f).injective
  change algebraRingDirectLimitEquiv S f
    ((algebraRingDirectLimitEquiv S f).symm (algebraMap A D a)) = _
  rw [RingEquiv.apply_symm_apply, algebraRingDirectLimitEquiv_of,
    _root_.DirectLimit.algebraMap_def (f := f) i]
  rfl
/-- ## 概要
共通基底の環余極限への標準写像から代数構造を定める。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
標準環準同型の toAlgebra を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
@[instance_reducible]
def algebraRingDirectLimitAlgebra : Algebra A L :=
  (algebraRingDirectLimitBaseMap S f).toAlgebra
attribute [local instance] algebraRingDirectLimitAlgebra

/-- ## 概要
環余極限への標準段射を共通基底上の代数射として実現する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
共通基底の標準写像が各段を経由する公式により係数との両立性を示す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitOf (i : ι) : S i →ₐ[A] L :=
  { ofL i with commutes' := fun a ↦ (algebraRingDirectLimitBaseMap_eq S f i a).symm }
/-- ## 概要
固定基底上で各段が I 完全忠実平坦なら、環余極限も同じ係数作用で I 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
余極限モデルの比較を元の係数作用について線形化し、代数余極限での保存を移す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem isCompletelyFaithfullyFlat_algebraRingDirectLimit (I : Ideal A)
    (hS : ∀ i, IsCompletelyFaithfullyFlat I (S i)) :
    IsCompletelyFaithfullyFlat I L := by
  let e := algebraRingDirectLimitEquiv S f
  let E : L ≃ₗ[A] D :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        change e (algebraRingDirectLimitBaseMap S f a * x) = algebraMap A D a * e x
        rw [map_mul]
        congr 1
        exact e.apply_symm_apply _ }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E.symm
    (isCompletelyFaithfullyFlat_algebraDirectLimit S f I hS)


/-- ## 概要
両立する段ごとの代数射は、環余極限からの共通基底上の代数射を誘導する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
環余極限の持上げを作り、基底の標準写像を任意の一段を経由させて係数との両立性を示す。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
def algebraRingDirectLimitLift {B : Type u} [CommRing B] [Algebra A B]
    (t : ∀ i, S i →ₐ[A] B)
    (ht : ∀ i j h x, t j (f i j h x) = t i x) : L →ₐ[A] B := by
  let q := Ring.DirectLimit.lift S (fun i j h ↦ AlgHom.toRingHom (f i j h)) B
    (fun i ↦ (t i).toRingHom) ht
  refine { q with commutes' := ?_ }
  intro a
  obtain ⟨i⟩ := ‹Nonempty ι›
  change q (algebraRingDirectLimitBaseMap S f a) = algebraMap A B a
  rw [algebraRingDirectLimitBaseMap_eq S f i a]
  have he : q (ofL i (algebraMap A (S i) a)) = t i (algebraMap A (S i) a) :=
    Ring.DirectLimit.lift_of ..
  rw [he, AlgHom.commutes]

/-- ## 概要
余極限からの代数射は標準段射上で与えられた代数射に一致する。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の代数構造を扱う。

## 方針
実際の環余極限の持上げの計算規則を使う。

## 規約
環と添字は Type u。束の型の違う余極限の環構造が定義的に一致するとは仮定しない。

## 使われ方
固定初段上の perfectoid 完全忠実平坦代数の圏で、超限反復の極限を構成する。
-/
theorem algebraRingDirectLimitLift_of {B : Type u} [CommRing B] [Algebra A B]
    (t : ∀ i, S i →ₐ[A] B) (ht : ∀ i j h x, t j (f i j h x) = t i x)
    (i : ι) (x : S i) : algebraRingDirectLimitLift S f t ht (ofL i x) = t i x := by
  exact Ring.DirectLimit.lift_of B (fun i ↦ (t i).toRingHom) ht i x
end SerrePositivity.BhattScholze.Andre.Transfinite

end AlgebraColimit

/-! ## CountableRelations -/

@[expose] public noncomputable section CountableRelations

open SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite
private lemma principal_smodEq_iff {S : Type*} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule S S))] ↔
      ∃ z, x - y = a ^ n * z := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  rfl

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
omit [Nonempty ι] in
include hbound in
/-- ## 概要
一段の元の可算族に関する等式が環余極限で成り立ち、可算添字集合が上界を持つなら、
すべての等式が同時に成り立つ後の段が存在する。
BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
各等式が成り立つ段を環余極限の零の判定で選び、それらの可算集合に共通上界を取る。

## 規約
環と添字は Type u。素数性・p 正則性・完全平坦性・単射性を追加しない。

## 使われ方
ω₁ 塔の終段において、任意の両立する環遷移射について自動的完備性を得る。
-/
theorem exists_stage_countable_equalities {κ : Type v} [Countable κ] (i : ι) (a b : κ → R i)
    (hab : ∀ x, Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (a x) =
      Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (b x)) :
    ∃ j, ∃ hij : i ≤ j, ∀ x, f i j hij (a x) = f i j hij (b x) := by
  classical
  have hz (x : κ) : Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (a x - b x) = 0 := by
    rw [map_sub, hab, sub_self]
  choose j hij hj using (fun x ↦ Ring.DirectLimit.of.zero_exact (hz x))
  obtain ⟨k, hk⟩ := hbound (Set.range j) (Set.countable_range j)
  obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
  refine ⟨l, hil, fun x ↦ sub_eq_zero.mp ?_⟩
  have hjl : j x ≤ l := (hk (j x) ⟨x, rfl⟩).trans hkl
  have he := congrArg (f (j x) l hjl) (hj x)
  simpa only [map_sub, map_zero, DirectedSystem.map_map' f] using he


include hbound in
/-- ## 概要
各段が p 進完備な有向系で、可算添字集合がすべて上界を持つなら、
環余極限は p 進完備である。遷移射の単射性は不要。
BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
分離性の冪割算の証人と、Cauchy 列の差の冪割算の証人を一段へ降ろす。
その後、可算個の等式も同時に後の段へ降ろし、そこで完備性を適用する。

## 規約
環と添字は Type u。素数性・p 正則性・完全平坦性・単射性を追加しない。

## 使われ方
ω₁ 塔の終段において、任意の両立する環遷移射について自動的完備性を得る。
-/
theorem isAdicComplete_directLimit_of_countable_upperBound_without_injective (p : ℕ)
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)] :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  classical
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let ofL := Ring.DirectLimit.of R (fun i j h ↦ f i j h)
  rw [isAdicComplete_iff]
  constructor
  · constructor
    intro x hx
    have hx' : ∀ n : ℕ, ∃ z : L, x = (p : L) ^ n * z := by
      intro n
      simpa only [sub_zero] using (principal_smodEq_iff (p : L) x 0 n).mp (hx n)
    choose d hd using hx'
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨j, d', hd'⟩ := exists_stage_countable_family R f hbound d
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hdivL : ∀ n, ofL k (f i k hik x) =
        ofL k ((p : R k) ^ n * f j k hjk (d' n)) := by
      intro n
      simpa only [ofL, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hd'] using hd n
    obtain ⟨l, hkl, hl⟩ := exists_stage_countable_equalities R f hbound k
      (fun _ : ℕ ↦ f i k hik x) (fun n ↦ (p : R k) ^ n * f j k hjk (d' n)) hdivL
    have hz : f k l hkl (f i k hik x) = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R l)}) (R l))
      intro n
      apply (principal_smodEq_iff (p : R l) _ 0 n).mpr
      refine ⟨f k l hkl (f j k hjk (d' n)), ?_⟩
      simpa only [sub_zero, map_mul, map_pow, map_natCast] using hl n
    rw [← Ring.DirectLimit.of_f hik x, ← Ring.DirectLimit.of_f hkl, hz, map_zero]
  · constructor
    intro a ha
    have hdiff : ∀ m n : ℕ, ∃ z : L, a m - a (m+n) = (p : L) ^ m * z := by
      intro m n
      exact (principal_smodEq_iff (p : L) (a m) (a (m+n)) m).mp (ha (Nat.le_add_right m n))
    choose d hd using hdiff
    obtain ⟨i, b, hb⟩ := exists_stage_countable_family R f hbound a
    obtain ⟨j, c, hc⟩ := exists_stage_countable_family R f hbound (Function.uncurry d)
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let b' : ℕ → R k := fun n ↦ f i k hik (b n)
    have heqL : ∀ mn : ℕ × ℕ, ofL k (b' mn.1 - b' (mn.1+mn.2)) =
        ofL k ((p : R k) ^ mn.1 * f j k hjk (c mn)) := by
      rintro ⟨m, n⟩
      simpa only [ofL, b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f,
        hb, hc, Function.uncurry_apply_pair] using hd m n
    obtain ⟨l, hkl, hl⟩ := exists_stage_countable_equalities R f hbound k
      (fun mn : ℕ × ℕ ↦ b' mn.1 - b' (mn.1+mn.2))
      (fun mn ↦ (p : R k) ^ mn.1 * f j k hjk (c mn)) heqL
    let b'' : ℕ → R l := fun n ↦ f k l hkl (b' n)
    have heq : ∀ m n, b'' m - b'' (m+n) =
        (p : R l) ^ m * f k l hkl (f j k hjk (c (m,n))) := by
      intro m n
      simpa only [b'', map_sub, map_mul, map_pow, map_natCast] using hl (m,n)
    obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : R l)}) b'' (by
      intro m n hmn
      apply (principal_smodEq_iff (p : R l) _ _ m).mpr
      refine ⟨f k l hkl (f j k hjk (c (m,n-m))), ?_⟩
      simpa only [Nat.add_sub_of_le hmn] using heq m (n-m))
    refine ⟨ofL l z, ?_⟩
    intro n
    obtain ⟨t, ht⟩ := (principal_smodEq_iff (p : R l) (b'' n) z n).mp (hz n)
    apply (principal_smodEq_iff (p : L) (a n) (ofL l z) n).mpr
    refine ⟨ofL l t, ?_⟩
    have he := congrArg (ofL l) ht
    simpa only [ofL, b'', b', map_sub, map_mul, map_pow, map_natCast,
      Ring.DirectLimit.of_f, hb] using he
include hbound in
/-- ## 概要
perfectoid 環の有向系で可算添字集合が上界を持つとき、環余極限自体が perfectoid となる。
BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
遷移射の単射性なしで証明した自動的完備性を用い、標準完備化との環同型によって
完備化の perfectoid 性を未完備余極限に移す。

## 規約
最小元を持つ有向添字を用いる。p 完全平坦性・単射性・p 正則性は要求しない。
零環を許す。環と添字は Type u。

## 使われ方
ω₁ 反復の終段で、根の存在を保った未完備余極限を perfectoid 環として使う。
-/
theorem isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound_without_flatness
    [OrderBot ι] (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, SerrePositivity.IsIntegralPerfectoid (R i) p) :
    SerrePositivity.IsIntegralPerfectoid (Ring.DirectLimit R (fun i j h ↦ f i j h)) p := by
  have hc (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    rcases hR i with hz | ⟨_, hc, _⟩
    · let := hz
      infer_instance
    · exact hc
  let (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := hc i
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let := isAdicComplete_directLimit_of_countable_upperBound_without_injective R f hbound p
  exact isIntegralPerfectoid_of_ringEquiv p
    (AdicCompletion.ofAlgEquiv (Ideal.span {(p : L)})).symm.toRingEquiv
    (isIntegralPerfectoid_adicCompletion_ringDirectLimit R f hR)

end SerrePositivity.BhattScholze.Andre.Transfinite

end CountableRelations

/-! ## ω₁ 塔の終段における三性質

BS 著者版 Theorem 7.14（著者版 p.61）の超限塔が与えられた後の合成を行う。
塔の存在を追加の公理や引用として宣言しない。
-/

@[expose] public noncomputable section Terminal

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open Ordinal Cardinal
/-- ## 概要
ω₁ の小さい添字型に最小元を与える。BS 著者版 Theorem 7.14（著者版 p.61）の初段に用いる。

## 方針
非空な整列線形順序の標準の最小元構造を使う。

## 規約
添字は Ordinal.ToType ω₁ のままで、Type u に留まる。

## 使われ方
最小段から終段への標準環準同型を指定する。
-/
instance omegaOneIndex_orderBot : OrderBot (Ordinal.ToType (ω₁ : Ordinal.{u})) :=
  WellFoundedLT.toOrderBot _

/-- ## 概要
ω₁ 添字の p 完全忠実平坦な perfectoid 塔で、各後続段が前段の全正次数モニック多項式の
根を持てば、環余極限は perfectoid かつ絶対整閉であり、初段からの標準射は p 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）の終段の三性質を合成する。

## 方針
可算添字集合の上界から完備性と perfectoid 性を得る。最小段からの完全忠実平坦性は
通常の有向余極限で保存する。多項式の有限係数を一段に降ろし、次段で根を取る。

## 規約
環と添字は Type u。塔は実際の環・遷移射・DirectedSystem として引数に与える。
塔自体の存在や一段拡大を新たな仮定なしで証明したことにはしない。

## 使われ方
訂正済み step による超限塔を構成した後、BS 著者版 Theorem 7.14 の結論を取り出す。
-/
theorem omegaOne_directLimit_properties
    (R : Ordinal.ToType (ω₁ : Ordinal.{u}) → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
      ∃ x : R (Order.succ i), P.eval₂ (f i (Order.succ i) (Order.le_succ i)) x = 0) :
    let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
    IsIntegralPerfectoid L p ∧
      (let := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
       IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) L) ∧
      IsAbsolutelyIntegrallyClosed L := by
  refine ⟨isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound
    R f hR hflat omegaOneIndex_countable_upperBound, ?_, ?_⟩
  · exact isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot R f (fun i ↦ hflat ⊥ i bot_le)
  · exact (omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed R f p hR hflat hroot).2
end SerrePositivity.BhattScholze.Andre.Transfinite

end Terminal

/-! ## AlgebraCategory -/

@[expose] public noncomputable section AlgebraCategory

open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
/-- ## 概要
固定初段 R 上で perfectoid かつ p 完全忠実平坦な代数を、標準係数環射とともに束ねる。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環と係数環射をデータとして保持し、perfectoid 性と、その射の toAlgebra に関する完全忠実平坦性を記録する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
structure AndreTowerAlgebra where
  carrier : Type u
  [commRing : CommRing carrier]
  baseMap : R →+* carrier
  perfectoid : IsIntegralPerfectoid carrier p
  flat : letI := baseMap.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) carrier
attribute [instance] AndreTowerAlgebra.commRing
/-- ## 概要
塔の代数の台集合を同じ Type u の環として使う。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
構造の carrier 射影を CoeSort に用いる。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebraCoeSort : CoeSort (AndreTowerAlgebra R p) (Type u) :=
  ⟨AndreTowerAlgebra.carrier⟩
/-- ## 概要
塔の代数に元の標準係数環射による R 代数構造を与える。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
保持している baseMap の toAlgebra を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebraAlgebra (X : AndreTowerAlgebra R p) : Algebra R X := X.baseMap.toAlgebra
namespace AndreTowerAlgebra
variable {R p}
/-- ## 概要
固定初段上の塔の代数の射を、係数環射と両立する環準同型として定める。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環準同型とその係数射との合成が終域の係数射に等しいという条件を保持する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
structure Hom (X Y : AndreTowerAlgebra R p) where
  toRingHom : X →+* Y
  commutes : toRingHom.comp X.baseMap = Y.baseMap
/-- ## 概要
塔の代数の射は、その環準同型が等しければ等しい。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
構造を場合分けし、両立性条件の証明無関係性を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
@[ext]
theorem Hom.ext {X Y : AndreTowerAlgebra R p} {f g : Hom X Y}
    (h : f.toRingHom = g.toRingHom) : f = g := by cases f; cases g; congr
/-- ## 概要
固定初段上の perfectoid 完全忠実平坦代数と、通常の係数両立環射は圏をなす。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
恒等・合成は元の環準同型のものとし、係数との両立性は環射の結合律から示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance category : Category (AndreTowerAlgebra R p) where
  Hom := Hom
  id X := ⟨RingHom.id X, by ext x; rfl⟩
  comp f g := ⟨g.toRingHom.comp f.toRingHom, by rw [RingHom.comp_assoc, f.commutes, g.commutes]⟩
  id_comp := by intros; ext x; rfl
  comp_id := by intros; ext x; rfl
  assoc := by intros; ext x; rfl
/-- ## 概要
塔の代数は通常の p 進完備性を持つ。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
perfectoid の定義の完備性を取り出し、零環の場合は標準インスタンスを使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
theorem complete (X : AndreTowerAlgebra R p) : IsAdicComplete (Ideal.span {(p : X)}) X := by
  rcases X.perfectoid with hz | ⟨_, hc, _⟩
  · let := hz
    infer_instance
  · exact hc
variable {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (F : ι ⥤ AndreTowerAlgebra R p)
/-- ## 概要
塔の代数の図式から各段の同じ宇宙の環の台集合を取り出す。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の対象の carrier を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def diagramRing (i : ι) : Type u := F.obj i
/-- ## 概要
取り出した図式の各段に元の可換環構造を与える。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の束ねた環の構造をそのまま返す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramCommRing (i : ι) : CommRing (diagramRing F i) :=
  inferInstanceAs (CommRing (F.obj i))
/-- ## 概要
取り出した図式の各段に元の固定初段の係数作用を与える。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
各対象の baseMap から既に定めた代数構造をそのまま使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramAlgebra (i : ι) : Algebra R (diagramRing F i) :=
  inferInstanceAs (Algebra R (F.obj i))
/-- ## 概要
塔の代数の函手から、共通基底上の有向系の代数遷移射を取り出す。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の射の環準同型と係数射の両立条件を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def diagramMap (i j : ι) (h : i ≤ j) : diagramRing F i →ₐ[R] diagramRing F j :=
  { (F.map (homOfLE h)).toRingHom with
    commutes' := fun r ↦ RingHom.congr_fun (F.map (homOfLE h)).commutes r }
/-- ## 概要
函手から取り出した環と遷移射は DirectedSystem の恒等・合成条件を満たす。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
函手の map_id と map_comp を元ごとの等式へ移す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance diagramSystem : DirectedSystem (diagramRing F) (fun i j h ↦ diagramMap F i j h) where
  map_self := by
    intro i x
    change (F.map (𝟙 i)).toRingHom x = x
    rw [F.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    have he := F.map_comp (homOfLE hij) (homOfLE hjk)
    exact (congrArg (fun t ↦ t.toRingHom x) he).symm
local notation "S" => diagramRing F
local notation "maps" => diagramMap F
local notation "L" => Ring.DirectLimit S (fun i j h ↦ AlgHom.toRingHom (maps i j h))
local notation "C" => AdicCompletion (Ideal.span {(p : L)}) L
local notation "ofL" => Ring.DirectLimit.of S (fun i j h ↦ AlgHom.toRingHom (maps i j h))
/-- ## 概要
最小元を持つ有向添字の塔の代数の図式に対し、環余極限の通常 p 進完備化は再び塔の代数となる。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
Fontaine 表示による完備化の perfectoid 性と、各段の共通基底上の完全忠実平坦性を使う。
余極限の p 冪ねじれの境界 1 により、標準完備化射との合成も完全忠実平坦となる。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitObject : AndreTowerAlgebra R p := by
  let β := algebraRingDirectLimitBaseMap S maps
  let map : R →+* C := (algebraMap L C).comp β
  refine ⟨C, map, ?_, ?_⟩
  · exact isIntegralPerfectoid_adicCompletion_ringDirectLimit S
      (fun i j h ↦ AlgHom.toRingHom (maps i j h)) (fun i ↦ (F.obj i).perfectoid)
  · apply isCompletelyFaithfullyFlat_adicCompletion_comp p β
    · exact isCompletelyFaithfullyFlat_algebraRingDirectLimit S maps _ (fun i ↦ (F.obj i).flat)
    · refine ⟨1, ?_⟩
      intro n x hx
      simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid S
        (fun i j h ↦ AlgHom.toRingHom (maps i j h)) p (fun i ↦ (F.obj i).perfectoid) n x hx

/-- ## 概要
各段から完備化した余極限対象への標準射を、固定初段上の射として実現する。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の環余極限の標準段射を完備化射と合成し、基底写像の各段での表示で係数両立性を示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitOf (i : ι) : F.obj i ⟶ colimitObject F where
  toRingHom := (algebraMap L C).comp (ofL i)
  commutes := by
    ext r
    change algebraMap L C (ofL i ((F.obj i).baseMap r)) =
      algebraMap L C (algebraRingDirectLimitBaseMap S maps r)
    rw [algebraRingDirectLimitBaseMap_eq S maps i r]
    rfl

/-- ## 概要
完備化した余極限対象と標準段射は元の図式の余錐をなす。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
環余極限の標準段射の両立性を完備化射で写す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitCocone : Cocone F where
  pt := colimitObject F
  ι :=
    { app := colimitOf F
      naturality := by
        intro i j h
        apply Hom.ext
        ext x
        change algebraMap L C (ofL j (maps i j (leOfHom h) x)) = algebraMap L C (ofL i x)
        exact congrArg (algebraMap L C) (Ring.DirectLimit.of_f
          (f := fun i j h ↦ AlgHom.toRingHom (maps i j h)) (leOfHom h) x) }

/-- ## 概要
任意の余錐に対し、完備化した余極限対象から余錐の頂点への標準射を構成する。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
元の環余極限の普遍代数射を作り、perfectoid な頂点の p 進完備性により延長する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitDesc (t : Cocone F) : colimitObject F ⟶ t.pt := by
  letI := algebraRingDirectLimitAlgebra S maps
  let α : ∀ i, S i →ₐ[R] t.pt := fun i ↦
    { (t.ι.app i).toRingHom with
      commutes' := fun r ↦ RingHom.congr_fun (t.ι.app i).commutes r }
  have hα : ∀ i j h x, α j (maps i j h x) = α i x := by
    intro i j h x
    exact congrArg (fun z ↦ z.toRingHom x) (t.w (homOfLE h))
  let q := algebraRingDirectLimitLift S maps α hα
  have hc := complete t.pt
  refine ⟨natAdicCompletionLift p q.toRingHom hc, ?_⟩
  ext r
  change natAdicCompletionLift p q.toRingHom hc
    (algebraMap L C (algebraRingDirectLimitBaseMap S maps r)) = t.pt.baseMap r
  rw [natAdicCompletionLift_of]
  exact q.commutes r

/-- ## 概要
余極限の標準普遍写像は各段射との合成で、与えられた余錐の射に一致する。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
通常完備化の標準延長と環余極限の持上げの計算規則を順に適用する。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
theorem colimitDesc_fac (t : Cocone F) (i : ι) :
    colimitOf F i ≫ colimitDesc F t = t.ι.app i := by
  apply Hom.ext
  ext x
  change natAdicCompletionLift p _ (complete t.pt) (algebraMap L C (ofL i x)) = _
  rw [natAdicCompletionLift_of]
  exact algebraRingDirectLimitLift_of S maps _ _ i x

/-- ## 概要
構成した完備化余極限の余錐は、塔の代数の圏で実際の余極限である。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
標準普遍写像の因子分解を使い、一意性を完備化の環射の一意性と元の環余極限の一意性で示す。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac := colimitDesc_fac F
  uniq t m hm := by
    apply Hom.ext
    have hc : IsAdicComplete (Ideal.span {(p : t.pt)}) t.pt := by
      rcases t.pt.perfectoid with hz | ⟨_, hc, _⟩
      · let := hz
        infer_instance
      · exact hc
    apply natAdicCompletion_ringHom_ext p hc
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    exact congrArg (fun z ↦ z.toRingHom x) ((hm i).trans (colimitDesc_fac F t i).symm)

end AndreTowerAlgebra
/-- ## 概要
任意の非空整列線形順序 Type u による、塔の代数の圏の余極限が存在する。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の補助構成。

## 方針
整列順序の最小元を選び、完備化した環余極限と検証した普遍性を使う。

## 規約
基底環・各対象の環・添字は Type u。圏の対象の集合自体は Type (u+1) に置く。
対象の性質と標準係数射を保持し、圏の射自体には追加の平坦性条件を課さない。

## 使われ方
訂正済み一段拡大を後続操作とし、Mathlib の整列超限反復へ余極限を供給する。
-/
instance andreTowerAlgebra_hasColimitsOfShape {ι : Type u}
    [LinearOrder ι] [Nonempty ι] [WellFoundedLT ι] :
    HasColimitsOfShape ι (AndreTowerAlgebra R p) := by
  let : OrderBot ι := WellFoundedLT.toOrderBot ι
  exact ⟨fun F ↦ ⟨⟨AndreTowerAlgebra.colimitCocone F, AndreTowerAlgebra.colimitIsColimit F⟩⟩⟩
end SerrePositivity.BhattScholze.Andre.Transfinite

end AlgebraCategory

/-! ## Existence -/

@[expose] public noncomputable section Existence

open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
variable (step : ∀ (B : Type u) [CommRing B] (_hB : IsIntegralPerfectoid B p)
    {σ : Type u} (f : σ → Polynomial B), (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
    ∃ (T : Type u) (_ : CommRing T) (φ : B →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0)
include step in
/-- ## 概要
固定初段上の塔の代数には、全正次数モニック多項式の根を含む後続対象への射が存在する。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
すべての正次数モニック多項式の部分型を添字とする族に指定 step を適用し、
初段からの完全忠実平坦性を元の係数射との合成で保持する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem exists_root_successor (X : AndreTowerAlgebra R p) :
    ∃ (Y : AndreTowerAlgebra R p) (φ : X ⟶ Y),
      ∀ (P : Polynomial X), P.Monic → 0 < P.natDegree →
        ∃ y : Y, P.eval₂ φ.toRingHom y = 0 := by
  let σ := {P : Polynomial X // P.Monic ∧ 0 < P.natDegree}
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    step X X.perfectoid (fun P : σ ↦ P.val) (fun P ↦ P.property)
  let := hTinst
  let β := φ.comp X.baseMap
  have hβ : letI := β.toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T :=
    isCompletelyFaithfullyFlat_natCast_comp X.baseMap φ p X.flat hφ
  let Y : AndreTowerAlgebra R p := ⟨T, β, hT, hβ⟩
  refine ⟨Y, ⟨φ, rfl⟩, ?_⟩
  intro P hP hdeg
  exact ⟨ρ ⟨P, hP, hdeg⟩, hroot ⟨P, hP, hdeg⟩⟩

/-- ## 概要
指定 step の存在証明から、塔の代数の後続対象を選ぶ。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
証明済みの後続対象の存在に Classical.choose を適用する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessor (X : AndreTowerAlgebra R p) : AndreTowerAlgebra R p :=
  (exists_root_successor R p step X).choose
/-- ## 概要
選んだ後続対象への、固定初段と両立する環射を選ぶ。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
同じ後続存在証明から射を取り出す。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessorMap (X : AndreTowerAlgebra R p) : X ⟶ rootSuccessor R p step X :=
  (exists_root_successor R p step X).choose_spec.choose
/-- ## 概要
選んだ後続対象は、前段の全正次数モニック多項式の根を持つ。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
後続存在証明の同じ選択に付随する根の存在条件を取り出す。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem rootSuccessorMap_roots (X : AndreTowerAlgebra R p) (P : Polynomial X)
    (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    ∃ y : rootSuccessor R p step X,
      P.eval₂ (rootSuccessorMap R p step X).toRingHom y = 0 :=
  (exists_root_successor R p step X).choose_spec.choose_spec P hP hdeg

/-- ## 概要
perfectoid な初段 R と指定 step から、Mathlib の超限反復用の後続操作を作る。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
零段は R 自身と恒等係数射とし、後続対象と射は一段拡大の選択を使う。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessorStructure (hR : IsIntegralPerfectoid R p) :
    SuccStruct (AndreTowerAlgebra R p) where
  X₀ := ⟨R, RingHom.id R, hR, isCompletelyFaithfullyFlat_self R (Ideal.span {(p : R)})⟩
  succ := rootSuccessor R p step
  toSucc := rootSuccessorMap R p step


/-- ## 概要
非空整列線形順序に沿う超限反復に必要な、塔の代数の圏の余極限条件が成り立つ。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
全体と各真の極限初期区間に、検証済みの整列添字余極限を供給する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
instance andreTowerAlgebra_hasIterationOfShape {J : Type u}
    [LinearOrder J] [Nonempty J] [WellFoundedLT J] :
    HasIterationOfShape J (AndreTowerAlgebra R p) where
  hasColimitsOfShape := inferInstance
  hasColimitsOfShape_of_isSuccLimit j hj := by
    let := hj.nonempty_Iio.to_subtype
    infer_instance

open Ordinal Cardinal in
/-- ## 概要
perfectoid 環 R には、perfectoid かつ絶対整閉な環 S への p 完全忠実平坦な代数構造が存在する。
ただし、正次数条件を追加した指定の一段拡大 step を明示仮定とする。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復。

## 方針
固定初段上の perfectoid・p 完全忠実平坦代数の圏で、全正次数モニックの根を添加する操作を
ω₁ まで反復する。真の極限段は環余極限の p 進完備化で構成する。終段には未完備余極限を使い、
可算データの降下でその自動的完備性を証明する。有限個の多項式係数が一段に入り、次段の根を
終段へ写すことで絶対整閉性を得る。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (hR : IsIntegralPerfectoid R p)
    (step : ∀ (B : Type u) [CommRing B] (_hB : IsIntegralPerfectoid B p)
    {σ : Type u} (f : σ → Polynomial B), (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
    ∃ (T : Type u) (_ : CommRing T) (φ : B →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  let J := Ordinal.ToType (ω₁ : Ordinal.{u})
  let Φ := rootSuccessorStructure R p step hR
  let F := Φ.iterationFunctor J
  let A := AndreTowerAlgebra.diagramRing F
  let f := AndreTowerAlgebra.diagramMap F
  let L := Ring.DirectLimit A (fun i j h ↦ (f i j h).toRingHom)
  let := algebraRingDirectLimitAlgebra A f
  have hperf : IsIntegralPerfectoid L p :=
    isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound_without_flatness A
      (fun i j h ↦ (f i j h).toRingHom) omegaOneIndex_countable_upperBound p
      (fun i ↦ (F.obj i).perfectoid)
  have hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) L :=
    isCompletelyFaithfullyFlat_algebraRingDirectLimit A f _ (fun i ↦ (F.obj i).flat)
  refine ⟨L, inferInstance, inferInstance, hperf, hflat, ?_⟩
  apply isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots A
    (fun i j h ↦ (f i j h).toRingHom)
  intro i P hP hdeg
  obtain ⟨y, hy⟩ := rootSuccessorMap_roots R p step (F.obj i) P hP hdeg
  let e := Φ.iterationFunctorObjSuccIso i (not_isMax i)
  refine ⟨Order.succ i, Order.le_succ i, e.inv.toRingHom y, ?_⟩
  have he : F.map (homOfLE (Order.le_succ i)) =
      rootSuccessorMap R p step (F.obj i) ≫ e.inv :=
    Φ.iterationFunctor_map_succ i (not_isMax i)
  change P.eval₂ ((F.map (homOfLE (Order.le_succ i))).toRingHom) (e.inv.toRingHom y) = 0
  rw [he]
  change P.eval₂ (e.inv.toRingHom.comp (rootSuccessorMap R p step (F.obj i)).toRingHom)
    (e.inv.toRingHom y) = 0
  rw [← Polynomial.hom_eval₂, hy, map_zero]
end SerrePositivity.BhattScholze.Andre.Transfinite

end Existence

/-! ## SingleRoot -/

@[expose] public noncomputable section SingleRoot

open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre
open SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
環同型 R≃S による係数作用について、S は任意のイデアル I に関して R 上完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Theorem 3.10（p.32）の一段拡大への適用。

## 方針
環同型を、元の R 作用と toAlgebra の作用の間の線形同型として扱い、R 自身の完全忠実平坦性を移す。

## 規約
環はすべて Type u。多項式は正次数モニックとし、p 正則性や追加の比較仮定は要求しない。
A1 の既証の有限 prism 商上の根付き拡大を使い、他レーンのファイルは変更しない。

## 使われ方
固定した多項式族を一元ずつ飽和させ、指定された任意族の step を構成する。
-/
theorem isCompletelyFaithfullyFlat_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    letI := e.toRingHom.toAlgebra; IsCompletelyFaithfullyFlat I S := by
  let := e.toRingHom.toAlgebra
  let E : R ≃ₗ[R] S :=
    { e.toAddEquiv with map_smul' := by intro r x; exact e.map_mul r x }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I E (isCompletelyFaithfullyFlat_self R I)
/-- ## 概要
任意の perfectoid 環 R 上の正次数モニック多項式は、p 完全忠実平坦な perfectoid 拡大で根を持つ。

## 方針
非零枝では既存の実 Fontaine・PD 構成による完全 prism 商表示に多項式を移し、
A1 の一元根付き拡大を適用する。元の基底との環同型が完全忠実平坦であることを示し、
標準射を合成する。零環枝では恒等射を使う。

## 規約
環はすべて Type u。多項式は正次数モニックとし、p 正則性や追加の比較仮定は要求しない。
A1 の既証の有限 prism 商上の根付き拡大を使い、他レーンのファイルは変更しない。

## 使われ方
固定した多項式族を一元ずつ飽和させ、指定された任意族の step を構成する。
-/
theorem exists_monicRootPerfectoidExtension (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (f : Polynomial R)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      f.eval₂ φ ρ = 0 := by
  classical
  rcases hR with hz | ⟨hp, hc, ⟨π, v, he⟩, hF, hk⟩
  · let := hz
    refine ⟨R, inferInstance, RingHom.id R, 0, Or.inl hz,
      isCompletelyFaithfullyFlat_self R _, Subsingleton.elim _ _⟩
  let := hc
  let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
  obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hk π v he
  let A := SerrePositivity.DerivedCompletion.PDCompletionH0 (WittVector p (PreTilt R p)) p d
  let := SerrePositivity.DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
  let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
    (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
  have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
    (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
  let Q := A ⧸ Ideal.span {P.generator}
  let F := f.map e.symm.toRingHom
  have hdegF : 0 < F.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
    exact hdeg
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    exists_monicRootPerfectoidExtension_of_perfectPrism P hP F (hf.map _) hdegF
  let := hTinst
  refine ⟨T, hTinst, φ.comp e.symm.toRingHom, ρ, hT,
    isCompletelyFaithfullyFlat_natCast_comp e.symm.toRingHom φ p
      (isCompletelyFaithfullyFlat_ringEquiv e.symm _) hφ, ?_⟩
  exact (Polynomial.eval₂_map _ _ _).symm.trans hroot
end SerrePositivity.BhattScholze.Andre.Transfinite

end SingleRoot

/-! ## FamilySaturation -/

@[expose] public noncomputable section FamilySaturation

open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    {σ : Type u} (f : σ → Polynomial R)
/-- ## 概要
固定基底 R の多項式族の一項が、塔の代数 X 内に根を持つという性質を表す。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
元の多項式を X の標準係数射で評価する存在命題を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def HasBasePolynomialRoot (X : AndreTowerAlgebra R p) (s : σ) : Prop :=
  ∃ x : X, (f s).eval₂ X.baseMap x = 0
/-- ## 概要
固定基底の多項式の根の存在は、塔の代数の任意の射に沿って保存される。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
根を環射で写し、係数射の両立性と評価の自然性を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem hasBasePolynomialRoot_map {X Y : AndreTowerAlgebra R p} (φ : X ⟶ Y) {s : σ}
    (h : HasBasePolynomialRoot f X s) : HasBasePolynomialRoot f Y s := by
  obtain ⟨x, hx⟩ := h
  refine ⟨φ.toRingHom x, ?_⟩
  rw [← φ.commutes, ← Polynomial.hom_eval₂, hx, map_zero]
variable (grow : ∀ (X : AndreTowerAlgebra R p) (s : σ),
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y), HasBasePolynomialRoot f Y s)
include grow in
/-- ## 概要
各多項式一項の根を持つ拡大があれば、全族の根を既に持つか、未解決の一項の根を新たに持つ後続対象を得る。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
全族が解決済みなら恒等射を使う。そうでなければ未解決の添字を選び、その一項の拡大を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem exists_rootAdvancement (X : AndreTowerAlgebra R p) :
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y),
      (∀ s, HasBasePolynomialRoot f X s) ∨
        ∃ s, ¬ HasBasePolynomialRoot f X s ∧ HasBasePolynomialRoot f Y s := by
  classical
  by_cases h : ∀ s, HasBasePolynomialRoot f X s
  · exact ⟨X, 𝟙 X, Or.inl h⟩
  obtain ⟨s, hs⟩ := not_forall.mp h
  obtain ⟨Y, φ, hy⟩ := grow X s
  exact ⟨Y, φ, Or.inr ⟨s, hs, hy⟩⟩
/-- ## 概要
未解決の一項を解決する後続対象を選ぶ。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
証明済みの一項前進の存在に Classical.choose を適用する。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def rootAdvancement (X : AndreTowerAlgebra R p) : AndreTowerAlgebra R p :=
  (exists_rootAdvancement f grow X).choose
/-- ## 概要
選んだ一項前進の対象への、固定基底と両立する射を取り出す。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
同じ存在証明の射の選択を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def rootAdvancementMap (X : AndreTowerAlgebra R p) : X ⟶ rootAdvancement f grow X :=
  (exists_rootAdvancement f grow X).choose_spec.choose
/-- ## 概要
選んだ後続対象では、全族が既に解決済みか、前段で未解決の一項が解決される。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
前進対象と射の同じ選択に付随する条件を取り出す。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem rootAdvancement_spec (X : AndreTowerAlgebra R p) :
    (∀ s, HasBasePolynomialRoot f X s) ∨
      ∃ s, ¬ HasBasePolynomialRoot f X s ∧
        HasBasePolynomialRoot f (rootAdvancement f grow X) s :=
  (exists_rootAdvancement f grow X).choose_spec.choose_spec
include grow in
/-- ## 概要
固定基底の任意の多項式族について、各対象・各一項に根を持つ拡大が可能なら、
全族の根を持つ一つの perfectoid・p 完全忠実平坦な代数が存在する。
BS 著者版 Theorem 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
添字族の濃度と可算濃度の上限の後続基数を取り、その始順序数に沿って未解決の一項を
解決する操作を反復する。終段で全族が解決しなければ、各段で新たに解決した添字は互いに異なる。
始順序数から元の添字族への単射が生じ、後続基数の定義に反する。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem exists_allBasePolynomialRoots (hR : IsIntegralPerfectoid R p) :
    ∃ X : AndreTowerAlgebra R p, ∀ s, HasBasePolynomialRoot f X s := by
  classical
  let c := Order.succ (Cardinal.mk σ ⊔ Cardinal.aleph0)
  let J := Ordinal.ToType c.ord
  have hc : Cardinal.aleph0 ≤ c := le_sup_right.trans (le_of_lt (Order.lt_succ _))
  have hlim := Cardinal.isSuccLimit_ord hc
  let : Nonempty J := Ordinal.nonempty_toType_iff.mpr hlim.ne_bot
  let : OrderBot J := WellFoundedLT.toOrderBot J
  let : NoMaxOrder J := by
    apply Ordinal.isSuccPrelimit_type_lt_iff.mp
    rw [Ordinal.type_toType]
    exact hlim.isSuccPrelimit
  let Φ : SuccStruct (AndreTowerAlgebra R p) :=
    { X₀ := ⟨R, RingHom.id R, hR, isCompletelyFaithfullyFlat_self R _⟩
      succ := rootAdvancement f grow
      toSucc := rootAdvancementMap f grow }
  let F := Φ.iterationFunctor J
  let Z := Φ.iteration J
  refine ⟨Z, ?_⟩
  by_contra hZ
  have hnot (i : J) : ¬ ∀ s, HasBasePolynomialRoot f (F.obj i) s := by
    intro hi
    exact hZ (fun s ↦ hasBasePolynomialRoot_map f ((Φ.iterationCocone J).ι.app i) (hi s))
  have hnew (i : J) : ∃ s, ¬ HasBasePolynomialRoot f (F.obj i) s ∧
      HasBasePolynomialRoot f (rootAdvancement f grow (F.obj i)) s :=
    (rootAdvancement_spec f grow (F.obj i)).resolve_left (hnot i)
  choose label hbefore hafter using hnew
  have hneq (i j : J) (hij : i < j) : label i ≠ label j := by
    intro heq
    apply hbefore j
    rw [← heq]
    let e := Φ.iterationFunctorObjSuccIso i (not_isMax i)
    have hi : HasBasePolynomialRoot f (F.obj (Order.succ i)) (label i) :=
      hasBasePolynomialRoot_map f e.inv (hafter i)
    exact hasBasePolynomialRoot_map f (F.map (homOfLE (Order.succ_le_of_lt hij))) hi
  have hinj : Function.Injective label := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hneq i j h heq
    · exact hneq j i h heq.symm
  have hcard : Cardinal.mk J ≤ Cardinal.mk σ := Cardinal.mk_le_of_injective hinj
  have hJ : Cardinal.mk J = c := by
    dsimp only [J]
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  rw [hJ] at hcard
  exact (not_le_of_gt (Order.lt_succ (Cardinal.mk σ ⊔ Cardinal.aleph0)))
    (hcard.trans le_sup_left)
end SerrePositivity.BhattScholze.Andre.Transfinite

end FamilySaturation

/-! ## FamilyExtension -/

@[expose] public noncomputable section FamilyExtension

open CategoryTheory
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    {σ : Type u} (f : σ → Polynomial R)
/-- ## 概要
固定基底 R の正次数モニック族の任意の一項は、任意の塔の代数からの拡大先で根を持つ。
BS 著者版 Theorem 7.14（著者版 p.61）の根添加の一段の存在。

## 方針
非零枝では元の多項式を係数射で移すと正次数モニックのままなので、一元根付き拡大を適用する。
初段の完全忠実平坦性は射の合成で保つ。零環枝では既に根がある。

## 規約
環と族の添字は Type u。入力は各多項式のモニック性と正次数のみ。
一段拡大 step 自体や、有限性・追加の平坦性・比較条件を仮定しない。

## 使われ方
指定された step と同じ型の証明を、BS 著者版 Theorem 7.14 の ω₁ 反復に入力する。
-/
theorem exists_familyRoot_successor (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    (X : AndreTowerAlgebra R p) (s : σ) :
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y), HasBasePolynomialRoot f Y s := by
  classical
  rcases subsingleton_or_nontrivial X with hz | hn
  · exact ⟨X, 𝟙 X, 0, hz.elim _ _⟩
  let := hn
  let P := (f s).map X.baseMap
  have hP : P.Monic := (hf s).map _
  have hPdeg : 0 < P.natDegree := by
    rw [(hf s).natDegree_map]
    exact hdeg s
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    exists_monicRootPerfectoidExtension X p X.perfectoid P hP hPdeg
  let := hTinst
  let β := φ.comp X.baseMap
  let Y : AndreTowerAlgebra R p :=
    ⟨T, β, hT, isCompletelyFaithfullyFlat_natCast_comp X.baseMap φ p X.flat hφ⟩
  refine ⟨Y, ⟨φ, rfl⟩, ρ, ?_⟩
  exact (Polynomial.eval₂_map _ _ _).symm.trans hroot

/-- ## 概要
perfectoid 環 R 上の任意の正次数モニック多項式族は、同じ p 完全忠実平坦な perfectoid 拡大内に根を持つ。
BS 著者版 Theorem 7.14（著者版 p.61）の根添加の一段の存在。

## 方針
各対象で一項の根を得る拡大を構成し、添字族より大きい後続基数による既証の飽和反復を使う。
終段の各根を選び、元の係数環射と perfectoid 性・完全忠実平坦性を取り出す。

## 規約
環と族の添字は Type u。入力は各多項式のモニック性と正次数のみ。
一段拡大 step 自体や、有限性・追加の平坦性・比較条件を仮定しない。

## 使われ方
指定された step と同じ型の証明を、BS 著者版 Theorem 7.14 の ω₁ 反復に入力する。
-/
theorem exists_monicFamilyRootedPerfectoidExtension (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) {σ : Type u} (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic ∧ 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  classical
  obtain ⟨X, hX⟩ := exists_allBasePolynomialRoots f
    (exists_familyRoot_successor f (fun s ↦ (hf s).1) (fun s ↦ (hf s).2)) hR
  change ∀ s, ∃ x : X, (f s).eval₂ X.baseMap x = 0 at hX
  choose ρ hρ using hX
  exact ⟨X, inferInstance, X.baseMap, ρ, X.perfectoid, X.flat, hρ⟩


end SerrePositivity.BhattScholze.Andre.Transfinite

end FamilyExtension

/-! ## BS 著者版 Theorem 7.14：André の完全忠実平坦な絶対整閉拡大

A1 の完全 prism 商上の一元根付き拡大を一般の perfectoid 基底へ移し、
固定した多項式族を一元ずつ飽和させて指定 step を証明する。
その step を ω₁ 反復へ入力する。追加の存在仮定や引用は置かない。
-/

@[expose] public noncomputable section Theorem714

namespace SerrePositivity.BhattScholze.Andre
/-- ## 概要
perfectoid 環 R には、perfectoid かつ絶対整閉な環 S への p 完全忠実平坦な代数構造が存在する（BS 著者版 Theorem 7.14 の第一文）。
R と S は同じ Type u に取る。

## 方針
A1 の一元根付き拡大を完全 prism 商表示から一般の perfectoid 基底へ移す。
固定した族を一元ずつ飽和させる後続基数の反復で、正次数条件付きの指定 step を得る。
全正次数モニック多項式の根添加を ω₁ まで反復する既証の存在定理へ、この step を入力する。

## 規約
前提は元の perfectoid 性のみ。一段拡大 step・塔・比較・ねじれ境界を仮定しない。
終段は自動的に p 進完備な環余極限を使い、有限係数の降下と次段の根から絶対整閉性を得る。

## 使われ方
Inputs の元の BS 著者版 Theorem 7.14 と同じ署名の、追加存在仮定なしの証明を供給する。
原典と異なる一段拡大の PD 経路と一元飽和の補足は計画ファイルに記録する。
-/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  apply Transfinite.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  intro B _ hB σ f hf
  exact Transfinite.exists_monicFamilyRootedPerfectoidExtension B p hB f hf
end SerrePositivity.BhattScholze.Andre

end Theorem714

/-! ## DirectedCompletion -/

@[expose] public noncomputable section DirectedCompletion

open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A R : ι → Type u) [∀ i, CommRing (A i)] [∀ i, CommRing (R i)]
    (fA : ∀ i j, i ≤ j → A i →+* A j) (fR : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem A (fun i j h ↦ fA i j h)] [DirectedSystem R (fun i j h ↦ fR i j h)]
    (θ : ∀ i, A i →+* R i)
    (hθ : ∀ i j h, (θ j).comp (fA i j h) = (fR i j h).comp (θ i))
local notation "LA" => Ring.DirectLimit A (fun i j h ↦ fA i j h)
local notation "LR" => Ring.DirectLimit R (fun i j h ↦ fR i j h)
local notation "ofA" => Ring.DirectLimit.of A (fun i j h ↦ fA i j h)
local notation "ofR" => Ring.DirectLimit.of R (fun i j h ↦ fR i j h)
/-- ## 概要
完全 δ 表示の核生成元が一段以降の全段で両立すれば、その像は余極限射の核を生成する。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Theorem 3.10（p.32）の極限操作を補足する。

## 方針
核の元を一段に代表し、零となる段と指定の基点段の共通上界へ移して単項核表示を使う。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem presentationLimitMap_ker_of_stage (i₀ : ι) (d : A i₀)
    (hker : ∀ j (h : i₀ ≤ j), RingHom.ker (θ j) = Ideal.span {fA i₀ j h d}) :
    RingHom.ker (presentationLimitMap A R fA fR θ hθ) = Ideal.span {ofA i₀ d} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of z
    have hz' : ofR i (θ i a) = 0 := by
      change presentationLimitMap A R fA fR θ hθ (ofA i a) = 0 at hz
      simpa only [presentationLimitMap_of] using hz
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz'
    have hja : θ j (fA i j hij a) = 0 :=
      (RingHom.congr_fun (hθ i j hij) a).trans hj
    obtain ⟨k, hjk, hi₀k⟩ := exists_ge_ge j i₀
    have hka : fA j k hjk (fA i j hij a) ∈ RingHom.ker (θ k) := by
      change θ k (fA j k hjk (fA i j hij a)) = 0
      rw [show θ k (fA j k hjk (fA i j hij a)) = fR j k hjk (θ j (fA i j hij a)) from
        RingHom.congr_fun (hθ j k hjk) _]
      rw [hja, map_zero]
    rw [hker k hi₀k] at hka
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hka
    apply Ideal.mem_span_singleton.mpr
    refine ⟨ofA k b, ?_⟩
    rw [← Ring.DirectLimit.of_f hij a, ← Ring.DirectLimit.of_f hjk (fA i j hij a),
      hb, map_mul, Ring.DirectLimit.of_f]
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change presentationLimitMap A R fA fR θ hθ (ofA i₀ d) = 0
    rw [presentationLimitMap_of]
    have hd : fA i₀ i₀ le_rfl d ∈ RingHom.ker (θ i₀) := by
      rw [hker i₀ le_rfl]
      exact Ideal.mem_span_singleton_self _
    have hd0 : θ i₀ d = 0 := by
      change θ i₀ (fA i₀ i₀ le_rfl d) = 0 at hd
      simpa only [DirectedSystem.map_self' fA] using hd
    rw [hd0, map_zero]
include hθ in
/-- ## 概要
非空有向系の完全 δ 表示で、一段の distinguished 元の像がその段以降の核を生成すれば、
表示先の余極限の p 進完備化は perfectoid である。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Theorem 3.10（p.32）の極限操作を補足する。

## 方針
完全 δ 構造を余極限へ移し、基点段以降の核表示から全体の単項核を同定する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem isIntegralPerfectoid_completion_of_eventual_presentation
    (D : ∀ i, DeltaStructure p (A i))
    (hδ : ∀ i j h, (D i).IsDeltaHom (D j) (fA i j h)) (hD : ∀ i, (D i).IsPerfect)
    (i₀ : ι) (d : A i₀) (hd : (D i₀).IsDistinguished d)
    (hs : ∀ i, Function.Surjective (θ i))
    (hk : ∀ j (h : i₀ ≤ j), RingHom.ker (θ j) = Ideal.span {fA i₀ j h d}) :
    IsIntegralPerfectoid (AdicCompletion (Ideal.span {(p : LR)}) LR) p := by
  let DL := deltaDirectLimitStructure A (fun i j h ↦ fA i j h) D (fun i j h x ↦ hδ i j h x)
  have hDL : DL.IsPerfect := deltaDirectLimit_isPerfect A fA D hδ hD
  have hdL : DL.IsDistinguished (ofA i₀ d) :=
    (deltaDirectLimitOf_isDeltaHom A (fun i j h ↦ fA i j h) D
      (fun i j h x ↦ hδ i j h x) i₀).map_isDistinguished hd
  exact isIntegralPerfectoid_adicCompletion_of_distinguished_kernel DL hDL (ofA i₀ d) hdL
    (presentationLimitMap A R fA fR θ hθ) (presentationLimitMap_surjective A R fA fR θ hθ hs)
    (presentationLimitMap_ker_of_stage A R fA fR θ hθ i₀ d hk)
end SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
各段で p が非単元な perfectoid 環の非空有向系について、余極限の通常 p 進完備化は perfectoid である。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Theorem 3.10（p.32）の極限操作を補足する。

## 方針
任意の一段の Fontaine 核の distinguished 生成元を選び、
その段以降に自然性で移して、基点段以降の表示による完備化判定を使う。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem isIntegralPerfectoid_completion_of_nonunit_directed_system
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Fact (¬ IsUnit (p : R i))]
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
        (Ring.DirectLimit R (fun i j h ↦ f i j h))) p := by
  have hdata (i : ι) :
      (∃ (π : R i) (v : (R i)ˣ), (p : R i) = v * π ^ p) ∧
      Function.Surjective (fun x : ModP (R i) p ↦ x ^ p) ∧
      (RingHom.ker (WittVector.fontaineTheta (R i) p)).IsPrincipal := by
    rcases hR i with hz | ⟨hp, hc, ht, hF, hk⟩
    · let := hz
      exact ((Fact.out : ¬ IsUnit (p : R i)) (isUnit_of_subsingleton _)).elim
    · exact ⟨ht, hF, hk⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨π, v, he⟩ := (hdata i₀).1
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator (R i₀) p
    (hdata i₀).2.1 (hdata i₀).2.2 π v he
  have hd0 : WittVector.fontaineTheta (R i₀) p d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  apply isIntegralPerfectoid_completion_of_eventual_presentation
    (fun i ↦ WittVector p (PreTilt (R i) p)) R
    (fun i j h ↦ ainfMap p (f i j h)) f
    (fun i ↦ WittVector.fontaineTheta (R i) p)
    (fun i j h ↦ fontaineTheta_natural p (f i j h))
    (fun i ↦ wittDeltaStructure p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap_delta p (f i j h))
    (fun i ↦ wittDeltaStructure_isPerfect p (PreTilt (R i) p)) i₀ d hd
  · intro i x
    exact surjective_fontaineTheta (hdata i).2.1 x
  · intro i h
    exact fontaineKernel_eq_span_image_distinguished p (f i₀ i h) d hd hd0 (hdata i).2.2
/-- ## 概要
perfectoid 環の任意の非空有向系の環余極限の通常 p 進完備化は perfectoid である。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Theorem 3.10（p.32）の極限操作を補足する。

## 方針
完備化が非零なら、各段から完備化への標準環射により全段の非零性を得る。
任意の基点段の Fontaine 表示を共通上界へ移す議論を適用する。零環枝は直接処理する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
theorem isIntegralPerfectoid_adicCompletion_of_directed_perfectoid
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
        (Ring.DirectLimit R (fun i j h ↦ f i j h))) p := by
  classical
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let C := AdicCompletion (Ideal.span {(p : L)}) L
  rcases subsingleton_or_nontrivial C with hz | hn
  · exact Or.inl hz
  let := hn
  have hdata (i : ι) : ∃ (hp : ¬ IsUnit (p : R i)),
      IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    let m : R i →+* C := (algebraMap L C).comp
      (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i)
    let : Nontrivial (R i) := m.domain_nontrivial
    rcases hR i with hz | ⟨hp, hc, _⟩
    · exact (zero_ne_one (Subsingleton.elim (0 : R i) 1)).elim
    · exact ⟨hp, hc⟩
  let : ∀ i, Fact (¬ IsUnit (p : R i)) := fun i ↦ ⟨(hdata i).choose⟩
  let : ∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i) := fun i ↦ (hdata i).choose_spec
  exact isIntegralPerfectoid_completion_of_nonunit_directed_system R f hR
end SerrePositivity.BhattScholze.Andre.Transfinite

namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
固定基底 B 上の p 完全忠実平坦な perfectoid 代数の非空有向系について、
環余極限の通常 p 進完備化への標準係数射も p 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限操作を補足する。

## 方針
共通係数作用での環余極限の完全忠実平坦性を用い、
perfectoid 各段から得る未完備余極限の p 冪ねじれ境界 1 を完備化の保存定理に入力する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性は要求しない。
基底の係数射は元の共通係数射と標準完備化射の合成そのものとする。

## 使われ方
任意の非空有向系の極限と完備化を通して、元の初段上の完全忠実平坦性を保つ。
-/
theorem isCompletelyFaithfullyFlat_completedAlgebraRingDirectLimit
    {B ι : Type u} [CommRing B] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
    [DirectedSystem S (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime] (hS : ∀ i, IsIntegralPerfectoid (S i) p)
    (hflat : ∀ i, IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) (S i)) :
    let L := Ring.DirectLimit S (fun i j h ↦ (f i j h).toRingHom)
    let C := AdicCompletion (Ideal.span {(p : L)}) L
    letI := ((algebraMap L C).comp (algebraRingDirectLimitBaseMap S f)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) C := by
  apply isCompletelyFaithfullyFlat_adicCompletion_comp p (algebraRingDirectLimitBaseMap S f)
  · exact isCompletelyFaithfullyFlat_algebraRingDirectLimit S f _ hflat
  · refine ⟨1, ?_⟩
    intro n x hx
    simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid S
      (fun i j h ↦ (f i j h).toRingHom) p hS n x hx
end SerrePositivity.BhattScholze.Andre.Transfinite

end DirectedCompletion

/-! ## André E3：BS 著者版 Theorem 7.14 の超限反復と証明済み存在定理

## 概要

BS 著者版 Theorem 7.14（著者版 p.61）の第一文を、追加の存在仮定なしで証明する。
一般の非空有向系の完備化の perfectoid 性と完全忠実平坦性も供給する。

## 方針

A1 の完全 prism 商上の一元拡大を任意の perfectoid 基底へ移す。
固定した族の一元飽和で指定 step を証明し、全正次数モニックの根添加を ω₁ まで反復する。
終段は自動的に p 進完備な未完備余極限を使い、有限係数の降下から絶対整閉性を得る。

## 規約

環と反復の添字は Type u に留める。元の初段の標準係数作用に関して完全忠実平坦性を証明する。
有向余極限の保存には、添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方

`SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`
が元の署名の無条件存在定理を供給する。
Inputs はこの無条件版の公開報告後、別保存単位で証明済み入口に置換した。
-/

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 7.14"] _root_.SerrePositivity.BhattScholze.Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
