module
public import SerrePositivity.CommutativeAlgebra.Reduced.PowerAnnihilator

public import Mathlib.Algebra.Colimit.Ring
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# perfectoid 塔の余極限の完備化と ω₁

## 概要
perfectoid 塔の未完備余極限と完備化の一様ねじれ境界、完備化した写像、perfectoid 有向系の完備化の余極限、表示の余極限、Type u 内の ω₁ と終段の完備性・根の存在、終段の絶対整閉性。
BS 著者版 Theorem 7.14 の証明の極限段に使う、perfectoid 塔の余極限と完備化を扱う。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Transfinite/Tower`。
-/

universe u

/-! ## Perfectoid 塔の未完備余極限と完備化の一様ねじれ境界

BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題を、被約性と逆極限の座標から証明する。
被約性・ねじれの境界と、完備化の perfectoid 性・完全忠実平坦性とは区別する。
-/

@[expose] public noncomputable section TorsionBound

open _root_.SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
/-- ## 概要
被約可換環の有向余極限は被約。BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
冪零元を一段へ降ろし、その冪が零になる関係を後の段に移して被約性を適用する。

## 規約
遷移写像の単射性は要求しない。

## 使われ方
perfectoid 塔の未完備余極限における p 冪ねじれの一様境界を得る。
-/
theorem isReduced_ringDirectLimit [∀ i, IsReduced (R i)] :
    IsReduced (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  refine ⟨fun z ⟨n, hn⟩ ↦ ?_⟩
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  have hz : Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (x ^ n) = 0 := by
    simpa only [map_pow] using hn
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz
  have hzero : f i j hij x = 0 := IsReduced.eq_zero _ ⟨n, by simpa only [map_pow] using hj⟩
  rw [← Ring.DirectLimit.of_f hij x, hzero, map_zero]

/-- ## 概要
perfectoid 可換環の有向余極限は、完備化前の段階で被約。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の補助命題。

## 方針
各段の証明済みの perfectoid 被約性を、被約環の有向余極限定理へ渡す。

## 規約
p ねじれと零環を許し、余極限の perfectoid 性を仮定・結論しない。

## 使われ方
可算極限段の完備化で使う共通の p 冪ねじれ境界を得る。
-/
theorem isReduced_ringDirectLimit_of_perfectoid (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsReduced (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  have (i : ι) : IsReduced (R i) := (hR i).isReduced (R i) p
  exact isReduced_ringDirectLimit R f

/-- ## 概要
perfectoid 塔の未完備有向余極限の p 冪ねじれは p 自身で消える。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段で、共通指数 1 を供給する。

## 方針
余極限の被約性から、一般の a 冪ねじれの境界を a=p に適用する。

## 規約
遷移写像の単射性や完全平坦性は不要。指数零も含む。

## 使われ方
p 進完備化の有界ねじれ比較の仮定を、具体的な指数で検証する。
-/
theorem ringDirectLimit_p_power_torsion_bound_of_perfectoid (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) (n : ℕ)
    (x : Ring.DirectLimit R (fun i j h ↦ f i j h)) (hx : (p : _) ^ n * x = 0) :
    (p : Ring.DirectLimit R (fun i j h ↦ f i j h)) * x = 0 := by
  have := isReduced_ringDirectLimit_of_perfectoid R f p hR
  exact _root_.SerrePositivity.CommutativeAlgebra.mul_eq_zero_of_pow_mul_eq_zero_of_reduced _ x n hx

/-- ## 概要
a 冪ねじれの共通境界 N は、主イデアル (a) による通常の完備化にも同じ N で保存される。
BS 著者版 Theorem 7.14（著者版 p.61）の可算極限段の補助命題。

## 方針
a^m で消える完備化の元を第 k+m 座標で調べる。元環のねじれ境界により、
a^N 倍した第 k 座標が零であることを示す。

## 規約
Noether 性、平坦性、a の非零因子性を要求しない。境界 N も指数 m も零を許す。

## 使われ方
perfectoid 塔の余極限における共通指数 1 を、通常の p 進完備化へ運ぶ。
-/
theorem adicCompletion_power_torsion_bound (R : Type u) [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (m : ℕ) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ m * x = 0) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ N * x = 0 := by
  obtain ⟨v, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {a}) R x
  apply AdicCompletion.ext_evalₐ
  intro k
  have hx' : a ^ m * v.val (k+m) ∈ (Ideal.span {a}) ^ (k+m) := by
    have he := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (k+m)) hx
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (k+m)) (a ^ m * v.val (k+m)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hdiff : a ^ m * (v.val (k+m) - a ^ k * z) = 0 := by
    rw [mul_sub, hz, pow_add]
    ring
  have hb := h m (v.val (k+m) - a ^ k * z) hdiff
  have hmem : a ^ N * v.val (k+m) ∈ (Ideal.span {a}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨a ^ N * z, ?_⟩
    rw [mul_sub] at hb
    calc
      a ^ N * v.val (k+m) = a ^ N * (a ^ k * z) := sub_eq_zero.mp hb
      _ = a ^ k * (a ^ N * z) := by ring
  have hdelta := v.property (Nat.le_add_right k m)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdelta
  have hn : a ^ N * v.val k ∈ (Ideal.span {a}) ^ k := by
    have he := ((Ideal.span {a}) ^ k).add_mem
      (((Ideal.span {a}) ^ k).mul_mem_left (a ^ N) hdelta) hmem
    simpa only [← mul_add, sub_add_cancel] using he
  change Ideal.Quotient.mk ((Ideal.span {a}) ^ k) (a ^ N * v.val k) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- ## 概要
perfectoid 塔の有向余極限を p 進完備化しても、p 冪ねじれは p 自身で消える。
BS 著者版 Theorem 7.14（著者版 p.61）の可算極限段に必要な一様境界。

## 方針
未完備余極限の被約性から共通指数 1 を得て、通常の完備化による境界保存を適用する。

## 規約
完備化環の被約性や perfectoid 性、完全忠実平坦性はここでは結論しない。
環と添字は Type u。

## 使われ方
通常完備化と導来完備化の比較に必要な有界ねじれ条件を供給する。
-/
theorem adicCompletion_ringDirectLimit_p_power_torsion_bound_of_perfectoid
    (p : ℕ) [Fact p.Prime] (hR : ∀ i, IsIntegralPerfectoid (R i) p) (n : ℕ)
    (x : AdicCompletion
      (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)))
    (hx : (p : _) ^ n * x = 0) : (p : _) * x = 0 := by
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  have hb : ∀ m : ℕ, ∀ y : L, (p : L) ^ m * y = 0 → (p : L) ^ 1 * y = 0 := by
    simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid R f p hR
  have he : algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) (p : L) =
      (p : AdicCompletion (Ideal.span {(p : L)}) L) := map_natCast _ _
  have hx' : (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) (p : L)) ^ n * x = 0 := by
    rw [he]
    exact hx
  simpa only [he, pow_one] using adicCompletion_power_torsion_bound L (p : L) 1 hb n x hx'

end SerrePositivity.BhattScholze.Andre.Transfinite

end TorsionBound

/-! ## CompletedMaps -/

@[expose] public noncomputable section CompletedMaps

open _root_.SerrePositivity _root_.SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
p 完全忠実平坦な写像の終域の p 冪ねじれが有界なら、その終域の通常 p 進完備化への合成も p 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
有界ねじれによる完備化の完全忠実平坦性を、元の写像の完全忠実平坦性と合成する。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_adicCompletion_comp {R T : Type u} [CommRing R] [CommRing T]
    (p : ℕ) (φ : R →+* T)
    (hφ : letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (hbound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
      (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0) :
    letI := ((algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)).comp φ).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (AdicCompletion (Ideal.span {(p : T)}) T) := by
  apply isCompletelyFaithfullyFlat_natCast_comp φ
    (algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)) p hφ
  exact isCompletelyFaithfullyFlat_adicCompletion_of_bounded_torsion T (p : T) hbound


/-- ## 概要
最小段から各段への写像が p 完全忠実平坦なら、環余極限への標準写像も p 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
最小段を共通係数環として各遷移射を代数射にする。非交和余極限との比較を
元の最小段の係数作用に関して線形化し、代数余極限の既証定理を移す。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot
    {p : ℕ} {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hflat : ∀ i, letI := (f ⊥ i bot_le).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) (R i)) :
    letI := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  let (i : ι) : Algebra (R ⊥) (R i) := (f ⊥ i bot_le).toAlgebra
  let g : ∀ i j, i ≤ j → R i →ₐ[R ⊥] R j := fun i j h ↦
    { f i j h with commutes' := fun r ↦ DirectedSystem.map_map' f bot_le h r }
  let : DirectedSystem R (fun i j h ↦ g i j h) := inferInstanceAs
    (DirectedSystem R (fun i j h ↦ f i j h))
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let D := _root_.DirectLimit R g
  let : Algebra (R ⊥) L := (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥).toAlgebra
  let a : L →+* D := Ring.DirectLimit.lift R (fun i j h ↦ f i j h) D
    (_root_.DirectLimit.Ring.of R g) (fun i j h x ↦ _root_.DirectLimit.Ring.of_f h x)
  let b : D →+* L := _root_.DirectLimit.Ring.lift R g L
    (Ring.DirectLimit.of R (fun i j h ↦ f i j h))
    (fun i j h x ↦ Ring.DirectLimit.of_f h x)
  have hba : b.comp a = RingHom.id L := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change b (a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x)) = _
    have ha : a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x) =
        _root_.DirectLimit.Ring.of R g i x := Ring.DirectLimit.lift_of ..
    rw [ha]
    rfl
  have hab : a.comp b = RingHom.id D := by
    apply _root_.DirectLimit.Ring.hom_ext
    intro i
    ext x
    change a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i x) = _
    exact Ring.DirectLimit.lift_of ..
  let e : L ≃+* D :=
    { a with
      invFun := b
      left_inv := RingHom.congr_fun hba
      right_inv := RingHom.congr_fun hab }
  have he (r : R ⊥) : e (algebraMap (R ⊥) L r) = algebraMap (R ⊥) D r := by
    change a (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥ r) = _
    trans (_root_.DirectLimit.Ring.of R g ⊥ r)
    · exact Ring.DirectLimit.lift_of ..
    · rw [_root_.DirectLimit.algebraMap_def (f := g) ⊥]
      have hself : algebraMap (R ⊥) (R ⊥) r = r := DirectedSystem.map_self' f r
      rw [hself]
      rfl
  let E : L ≃ₗ[R ⊥] D :=
    { e.toAddEquiv with
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        change e (algebraMap (R ⊥) L r * x) = algebraMap (R ⊥) D r * e x
        rw [map_mul, he] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R ⊥)}) E.symm
    (isCompletelyFaithfullyFlat_algebraDirectLimit R g _ hflat)


/-- ## 概要
perfectoid 環の有向系で、最小段から各段への写像が p 完全忠実平坦なら、
余極限の通常 p 進完備化への標準合成も p 完全忠実平坦である。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段の標準射を扱う。

## 方針
環余極限への標準写像の完全忠実平坦性と、perfectoid 環の余極限の
p 冪ねじれの境界 1 を、完備化への合成定理に入力する。

## 規約
環と添字は Type u とし、標準段射・標準完備化射そのものを用いる。
p 正則性・Noether 性・遷移射の単射性を要求しない。

## 使われ方
超限反復の極限段で、初段からの完全忠実平坦性を維持する。
-/
theorem isCompletelyFaithfullyFlat_completedRingDirectLimit_of_orderBot {p : ℕ} [Fact p.Prime]
    {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i, letI := (f ⊥ i bot_le).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) (R i)) :
    let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
    let C := AdicCompletion (Ideal.span {(p : L)}) L
    letI := ((algebraMap L C).comp
      (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R ⊥)}) C := by
  apply isCompletelyFaithfullyFlat_adicCompletion_comp p
    (Ring.DirectLimit.of R (fun i j h ↦ f i j h) ⊥)
    (isCompletelyFaithfullyFlat_ringDirectLimit_of_orderBot R f hflat)
  refine ⟨1, ?_⟩
  intro n x hx
  simpa only [pow_one] using
    ringDirectLimit_p_power_torsion_bound_of_perfectoid R f p hR n x hx
end SerrePositivity.BhattScholze.Andre.Transfinite

end CompletedMaps

/-! ## PresentationColimit -/

@[expose] public noncomputable section PresentationColimit

open _root_.SerrePositivity _root_.SerrePositivity.BhattScholze
open _root_.SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι]
    (A R : ι → Type u) [∀ i, CommRing (A i)] [∀ i, CommRing (R i)]
    (fA : ∀ i j, i ≤ j → A i →+* A j) (fR : ∀ i j, i ≤ j → R i →+* R j)
    (θ : ∀ i, A i →+* R i)
    (hθ : ∀ i j h, (θ j).comp (fA i j h) = (fR i j h).comp (θ i))
local notation "LA" => Ring.DirectLimit A (fun i j h ↦ fA i j h)
local notation "LR" => Ring.DirectLimit R (fun i j h ↦ fR i j h)
local notation "ofA" => Ring.DirectLimit.of A (fun i j h ↦ fA i j h)
local notation "ofR" => Ring.DirectLimit.of R (fun i j h ↦ fR i j h)
/-- ## 概要
両立する表示射の余極限射を作る。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限操作の補助命題。

## 方針
各段の表示射を終域の標準段射と合成し、環余極限の普遍性を使う。

## 規約
環と添字は Type u とし、遷移射の単射性や p 正則性は仮定しない。

## 使われ方
perfectoid 塔の Fontaine 表示から極限段の perfectoid 性を導く。
-/
def presentationLimitMap : LA →+* LR :=
  Ring.DirectLimit.lift A (fun i j h ↦ fA i j h) LR
    (fun i ↦ (ofR i).comp (θ i)) (by
      intro i j h a
      change ofR j (θ j (fA i j h a)) = ofR i (θ i a)
      rw [show θ j (fA i j h a) = fR i j h (θ i a) from RingHom.congr_fun (hθ i j h) a]
      exact Ring.DirectLimit.of_f h _)
/-- ## 概要
表示の余極限射は各標準段射上で元の表示射と一致する。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限操作の補助命題。

## 方針
余極限の持上げの計算規則を使う。

## 規約
環と添字は Type u とし、遷移射の単射性や p 正則性は仮定しない。

## 使われ方
perfectoid 塔の Fontaine 表示から極限段の perfectoid 性を導く。
-/
@[simp] theorem presentationLimitMap_of (i : ι) (a : A i) :
    presentationLimitMap A R fA fR θ hθ (ofA i a) = ofR i (θ i a) :=
  Ring.DirectLimit.lift_of ..

/-- ## 概要
各段の表示射が全射なら、その余極限射も全射である。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限操作の補助命題。

## 方針
余極限の元を一段で代表し、その段で原像を選ぶ。

## 規約
環と添字は Type u とし、遷移射の単射性や p 正則性は仮定しない。

## 使われ方
perfectoid 塔の Fontaine 表示から極限段の perfectoid 性を導く。
-/
theorem presentationLimitMap_surjective [Nonempty ι] [IsDirectedOrder ι]
    (hθsurj : ∀ i, Function.Surjective (θ i)) :
    Function.Surjective (presentationLimitMap A R fA fR θ hθ) := by
  intro x
  obtain ⟨i, r, rfl⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨a, rfl⟩ := hθsurj i r
  exact ⟨ofA i a, presentationLimitMap_of A R fA fR θ hθ i a⟩

/-- ## 概要
最小段の元の像が各段の核を生成すれば、その元は余極限射の核も生成する。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限操作の補助命題。

## 方針
核の元と零になる等式を後の段に移し、そこでの単項核表示を使う。

## 規約
環と添字は Type u とし、遷移射の単射性や p 正則性は仮定しない。

## 使われ方
perfectoid 塔の Fontaine 表示から極限段の perfectoid 性を導く。
-/
theorem presentationLimitMap_ker [OrderBot ι] [IsDirectedOrder ι]
    [DirectedSystem A (fun i j h ↦ fA i j h)] [DirectedSystem R (fun i j h ↦ fR i j h)]
    (d : A ⊥) (hker : ∀ i, RingHom.ker (θ i) = Ideal.span {fA ⊥ i bot_le d}) :
    RingHom.ker (presentationLimitMap A R fA fR θ hθ) = Ideal.span {ofA ⊥ d} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of z
    have hz' : ofR i (θ i a) = 0 := by
      change presentationLimitMap A R fA fR θ hθ (ofA i a) = 0 at hz
      simpa only [presentationLimitMap_of] using hz
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz'
    have hja : fA i j hij a ∈ RingHom.ker (θ j) := by
      change θ j (fA i j hij a) = 0
      exact (RingHom.congr_fun (hθ i j hij) a).trans hj
    rw [hker j] at hja
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hja
    apply Ideal.mem_span_singleton.mpr
    refine ⟨ofA j b, ?_⟩
    rw [← Ring.DirectLimit.of_f hij a, hb, map_mul, Ring.DirectLimit.of_f]
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change presentationLimitMap A R fA fR θ hθ (ofA ⊥ d) = 0
    rw [presentationLimitMap_of]
    have hd : fA ⊥ ⊥ bot_le d ∈ RingHom.ker (θ ⊥) := by
      rw [hker ⊥]
      exact Ideal.mem_span_singleton_self _
    have hdzero : θ ⊥ d = 0 := by
      change θ ⊥ (fA ⊥ ⊥ bot_le d) = 0 at hd
      simpa only [DirectedSystem.map_self' fA] using hd
    rw [hdzero, map_zero]

include hθ in
/-- ## 概要
完全 δ 環による両立する全射表示と共通の distinguished 核生成元があれば、表示先の環余極限の p 進完備化は perfectoid である。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限操作の補助命題。

## 方針
完全 δ 構造を余極限へ移し、全射と単項核を同定して通常完備化の既証定理を適用する。

## 規約
環と添字は Type u とし、遷移射の単射性や p 正則性は仮定しない。

## 使われ方
perfectoid 塔の Fontaine 表示から極限段の perfectoid 性を導く。
-/
theorem isIntegralPerfectoid_adicCompletion_of_presentationDiagram [OrderBot ι] [IsDirectedOrder ι]
    [DirectedSystem A (fun i j h ↦ fA i j h)] [DirectedSystem R (fun i j h ↦ fR i j h)]
    (D : ∀ i, DeltaStructure p (A i))
    (hδ : ∀ i j h, (D i).IsDeltaHom (D j) (fA i j h))
    (hD : ∀ i, (D i).IsPerfect)
    (d : A ⊥) (hd : (D ⊥).IsDistinguished d)
    (hθsurj : ∀ i, Function.Surjective (θ i))
    (hker : ∀ i, RingHom.ker (θ i) = Ideal.span {fA ⊥ i bot_le d}) :
    IsIntegralPerfectoid (AdicCompletion (Ideal.span {(p : LR)}) LR) p := by
  let DL := deltaDirectLimitStructure A (fun i j h ↦ fA i j h) D (fun i j h x ↦ hδ i j h x)
  have hDL : DL.IsPerfect := deltaDirectLimit_isPerfect A fA D hδ hD
  have hdL : DL.IsDistinguished (ofA ⊥ d) :=
    (deltaDirectLimitOf_isDeltaHom A (fun i j h ↦ fA i j h) D
      (fun i j h x ↦ hδ i j h x) ⊥).map_isDistinguished hd
  exact isIntegralPerfectoid_adicCompletion_of_distinguished_kernel DL hDL (ofA ⊥ d) hdL
    (presentationLimitMap A R fA fR θ hθ) (presentationLimitMap_surjective A R fA fR θ hθ hθsurj)
    (presentationLimitMap_ker A R fA fR θ hθ d hker)
end SerrePositivity.BhattScholze.Andre.Transfinite

end PresentationColimit

/-! ## PerfectoidCompletionColimit -/

@[expose] public noncomputable section PerfectoidCompletionColimit

open _root_.SerrePositivity _root_.SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (p : ℕ) [Fact p.Prime]
/-- ## 概要
環準同型が誘導する Fontaine 環の標準写像を定める。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
mod p の写像を Perfection と WittVector に順に移す。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
def ainfMap {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (f : R →+* S) :
    WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) :=
  WittVector.map (Perfection.map p (modPMap p f))
/-- ## 概要
恒等環準同型が誘導する Fontaine 環の写像は恒等である。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
Witt 係数と Perfection の係数を順に比較する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_id {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    (x : WittVector p (PreTilt R p)) : ainfMap p (RingHom.id R) x = x := by
  apply WittVector.ext
  intro n
  simp only [ainfMap, WittVector.map_coeff]
  apply Perfection.ext
  intro m
  change modPMap p (RingHom.id R) (PreTilt.coeff m (x.coeff n)) =
    PreTilt.coeff m (x.coeff n)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff m (x.coeff n))
  rw [← hr]
  rfl
/-- ## 概要
Fontaine 環の標準写像は環準同型の合成を保つ。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
各 Witt 係数の各 Perfection 成分を mod p の代表元で比較する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] [Fact (¬ IsUnit (p : T))]
    (f : R →+* S) (g : S →+* T) (x : WittVector p (PreTilt R p)) :
    ainfMap p (g.comp f) x = ainfMap p g (ainfMap p f x) := by
  apply WittVector.ext
  intro n
  simp only [ainfMap, WittVector.map_coeff]
  apply Perfection.ext
  intro m
  change modPMap p (g.comp f) (PreTilt.coeff m (x.coeff n)) =
    modPMap p g (modPMap p f (PreTilt.coeff m (x.coeff n)))
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff m (x.coeff n))
  rw [← hr]
  rfl


/-- ## 概要
Fontaine 環の標準写像は標準 δ 構造を保つ。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
既存の完全係数環上の Witt 写像の δ 自然性を適用する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_delta {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (f : R →+* S) :
    (wittDeltaStructure p (PreTilt R p)).IsDeltaHom
      (wittDeltaStructure p (PreTilt S p)) (ainfMap p f) :=
  wittDeltaStructure_map_isDeltaHom p (PreTilt R p) (Perfection.map p (modPMap p f))

variable {ι : Type u} [Preorder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Fact (¬ IsUnit (p : R i))]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
/-- ## 概要
環の有向系から Fontaine 環の有向系を得る。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
標準写像の恒等と合成の公式に元の有向系の公理を適用する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
instance ainfSystem : DirectedSystem (fun i ↦ WittVector p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap p (f i j h)) where
  map_self := by
    intro i x
    have he : f i i le_rfl = RingHom.id (R i) := by ext y; exact DirectedSystem.map_self' f y
    rw [he]
    exact ainfMap_id p x
  map_map := by
    intro k j i hij hjk x
    have he : f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij) := by
      ext y
      exact (DirectedSystem.map_map' f hij hjk y).symm
    rw [he]
    exact (ainfMap_comp p _ _ x).symm


include f in
 private theorem perfectoid_limit [OrderBot ι] [IsDirectedOrder ι]
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)]
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
  obtain ⟨π, v, he⟩ := (hdata ⊥).1
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator (R ⊥) p
    (hdata ⊥).2.1 (hdata ⊥).2.2 π v he
  have hd0 : WittVector.fontaineTheta (R ⊥) p d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  apply isIntegralPerfectoid_adicCompletion_of_presentationDiagram
    (fun i ↦ WittVector p (PreTilt (R i) p)) R
    (fun i j h ↦ ainfMap p (f i j h)) f
    (fun i ↦ WittVector.fontaineTheta (R i) p)
    (fun i j h ↦ fontaineTheta_natural p (f i j h))
    (fun i ↦ wittDeltaStructure p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap_delta p (f i j h))
    (fun i ↦ wittDeltaStructure_isPerfect p (PreTilt (R i) p)) d hd
  · intro i x
    exact surjective_fontaineTheta (hdata i).2.1 x
  · intro i
    exact fontaineKernel_eq_span_image_distinguished p (f ⊥ i bot_le) d hd hd0 (hdata i).2.2


end SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite

/-- ## 概要
最小元を持つ有向添字上の perfectoid 環の有向系について、環余極限の p 進完備化は perfectoid である。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 3.10（p.32）、BS 著者版 Theorem 7.14（p.61）の極限操作を補足する。

## 方針
各段の Fontaine 全射を自然性により余極限へ移す。最小段の distinguished 核生成元の像が
全段の核を生成するので、余極限も完全 δ 環の distinguished 商となる。零環の場合は別に処理する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem isIntegralPerfectoid_adicCompletion_ringDirectLimit {p : ℕ} [Fact p.Prime]
    {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
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
  exact perfectoid_limit p R f hR
/-- ## 概要
perfectoid 環の p 完全忠実平坦な有向系で、添字の可算部分集合が上界を持つとき、
環余極限自体が perfectoid となる。BS 著者版 Theorem 7.14（著者版 p.61）の非可算共終性の極限段。

## 方針
可算データの降下から余極限の p 進完備性を得て、標準完備化との環同型により
完備化の perfectoid 性を余極限自身に移す。

## 規約
最小元を持つ有向添字を用いる。零環と p ねじれを許す。環と添字は Type u。

## 使われ方
ω₁ の終段で完備化を追加せず perfectoid 環を得る。
-/
theorem isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j) :
    IsIntegralPerfectoid (Ring.DirectLimit R (fun i j h ↦ f i j h)) p := by
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let := isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat R f p hR hflat hbound
  exact isIntegralPerfectoid_of_ringEquiv p
    (AdicCompletion.ofAlgEquiv (Ideal.span {(p : L)})).symm.toRingEquiv
    (isIntegralPerfectoid_adicCompletion_ringDirectLimit R f hR)

end SerrePositivity.BhattScholze.Andre.Transfinite

end PerfectoidCompletionColimit

/-! ## 超限反復の終段における絶対整閉性

BS 著者版 Theorem 7.14（著者版 p.61）の超限反復に必要な根の移送を扱う。
極限環の完備性・perfectoid性・完全忠実平坦性はこのファイルでは主張しない。
-/

@[expose] public noncomputable section RootClosure

open _root_.Polynomial
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)

/-- ## 概要
各段の正次数モニック多項式が後の段で根を持てば、有向余極限は絶対整閉である。
BS 著者版 Theorem 7.14（著者版 p.61）の超限反復の最後の根の存在を実現する。

## 方針
Mathlib の有限係数の降下からモニックかつ同次数の多項式を選び、後の段の根を余極限へ送る。

## 規約
遷移写像の単射性、環の非零性、添字の非可算共終性はこの代数的結論には不要。
正の次数条件を必須とし、定数多項式 `1` の根を要求しない。

## 使われ方
完備な超限塔を別途構成した後、その終段の絶対整閉性を証明する。
-/
theorem isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
    ∃ (j : ι) (hij : i ≤ j) (x : R j), P.eval₂ (f i j hij) x = 0) :
    IsAbsolutelyIntegrallyClosed (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  classical
  intro P hP hdeg
  obtain ⟨i, Q, hQ⟩ := Ring.DirectLimit.Polynomial.exists_of P
  obtain ⟨Q', hmap, hdegree, hmonic⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts _ |>.mpr ⟨Q, hQ⟩) hP
  obtain ⟨j, hij, x, hx⟩ := hroot i Q' hmonic (hdegree ▸ hdeg)
  refine ⟨Ring.DirectLimit.of R (fun i j h ↦ f i j h) j x, ?_⟩
  rw [IsRoot, ← hmap, eval_map]
  have hcompat : (Ring.DirectLimit.of R (fun i j h ↦ f i j h) j).comp (f i j hij) =
      Ring.DirectLimit.of R (fun i j h ↦ f i j h) i := by
    ext a
    exact Ring.DirectLimit.of_f hij a
  rw [← hcompat, ← hom_eval₂, hx, map_zero]
end SerrePositivity.BhattScholze.Andre.Transfinite

end RootClosure

/-! ## Type u 内の ω₁ と終段の完備性・根の存在

BS 著者版 Theorem 7.14（著者版 p.61）の超限反復のため、ω₁ 未満の段を
`Ordinal.ToType` で同じ宇宙に表し、可算データの上界を実証明する。
-/

@[expose] public noncomputable section OmegaOne

namespace SerrePositivity.BhattScholze.Andre.Transfinite
open _root_.Ordinal _root_.Cardinal

/-- ## 概要
ω₁ 未満の順序数の Type u 表現は空でない。BS 著者版 Theorem 7.14（著者版 p.61）の塔の添字。

## 方針
正の順序数の ToType が空でないことを使う。

## 規約
Ordinal 自体の宇宙を塔の添字に持ち込まず、Ordinal.ToType を使う。

## 使われ方
同じ宇宙で有向余極限を構成する際の非空性を与える。
-/
instance omegaOneIndex_nonempty : Nonempty (Ordinal.ToType (ω₁ : Ordinal.{u})) :=
  Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'

/-- ## 概要
ω₁ 未満の段には最大段がない。BS 著者版 Theorem 7.14（著者版 p.61）の後続段の存在を表す。

## 方針
ω₁ が極限順序数であることを ToType の順序へ移す。

## 規約
ToType の標準 SuccOrder を使い、別の後続写像は定義しない。

## 使われ方
各段の多項式の根を必ず真に後の段に添加する。
-/
instance omegaOneIndex_noMaxOrder : NoMaxOrder (Ordinal.ToType (ω₁ : Ordinal.{u})) := by
  apply Ordinal.isSuccPrelimit_type_lt_iff.mp
  rw [Ordinal.type_toType]
  exact (Cardinal.isSuccLimit_omega 1).isSuccPrelimit

/-- ## 概要
Type u に表した ω₁ 未満の段の任意の可算集合には上界がある。
BS 著者版 Theorem 7.14（著者版 p.61）の終段で、可算データを一段へ降ろす根拠となる。

## 方針
各段を ω₁ 未満の順序数に戻し、可算上限も ω₁ 未満であることを使う。

## 規約
上界も Ordinal.ToType ω₁ の元として与え、宇宙を増やさない。

## 使われ方
終段の自動的な p 進完備性を、上界条件なしの ω₁ 特化版として供給する。
-/
theorem omegaOneIndex_countable_upperBound
    (s : Set (Ordinal.ToType (ω₁ : Ordinal.{u}))) (hs : s.Countable) :
    ∃ j, ∀ i ∈ s, i ≤ j := by
  classical
  let g : s → Ordinal.{u} := fun i ↦ (Ordinal.ToType.toOrd i.val).val
  have hb : (⨆ i, g i) < (ω₁ : Ordinal.{u}) := by
    let := hs.to_subtype
    exact Ordinal.iSup_lt_omega_one (fun i ↦ (Ordinal.ToType.toOrd i.val).property)
  refine ⟨Ordinal.ToType.mk ⟨⨆ i, g i, hb⟩, ?_⟩
  intro i hi
  calc
    i = Ordinal.ToType.mk (Ordinal.ToType.toOrd i) := (Ordinal.ToType.mk.apply_symm_apply i).symm
    _ ≤ Ordinal.ToType.mk ⟨⨆ i, g i, hb⟩ := by
      apply Ordinal.ToType.mk.monotone
      change g ⟨i, hi⟩ ≤ iSup g
      exact le_ciSup (f := g) Ordinal.bddAbove_of_small ⟨i, hi⟩

/-- ## 概要
ω₁ 添字の p 完全忠実平坦な perfectoid 塔で各後続段が前段の正次数モニックの根を持てば、
終段は p 進完備かつ絶対整閉。BS 著者版 Theorem 7.14（著者版 p.61）の終段の二つの性質。

## 方針
ω₁ の可算集合の上界を完備性定理に適用し、多項式は有限係数の降下と後続段の根から処理する。

## 規約
環と添字は Type u。塔は実際の環・遷移写像・DirectedSystem として与える。
終段の perfectoid 性・完全忠実平坦性や塔の存在は結論しない。

## 使われ方
極限段の保存定理と超限再帰で塔を構成した後、終段の完備性と絶対整閉性を同時に供給する。
-/
theorem omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed
    (R : Ordinal.ToType (ω₁ : Ordinal.{u}) → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, letI := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
      ∃ x : R (Order.succ i), P.eval₂ (f i (Order.succ i) (Order.le_succ i)) x = 0) :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) ∧
    IsAbsolutelyIntegrallyClosed (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  refine ⟨isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat
    R f p hR hflat omegaOneIndex_countable_upperBound, ?_⟩
  apply isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
  intro i P hP hdeg
  obtain ⟨x, hx⟩ := hroot i P hP hdeg
  exact ⟨Order.succ i, Order.le_succ i, x, hx⟩

end SerrePositivity.BhattScholze.Andre.Transfinite

end OmegaOne
