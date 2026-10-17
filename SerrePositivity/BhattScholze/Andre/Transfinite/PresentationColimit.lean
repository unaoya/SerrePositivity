module

public import SerrePositivity.BhattScholze.Andre.Transfinite.PrismaticCompletion
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectDeltaColimit
open SerrePositivity SerrePositivity.BhattScholze
open SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u
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
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限操作の補助命題。

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
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限操作の補助命題。

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
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限操作の補助命題。

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
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限操作の補助命題。

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
BS Lemma 3.9（著者版 pp.31–32）、Thm 7.14（p.61）の極限操作の補助命題。

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
