module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaColimit
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion

/-!
# δ 環の完全化と、完全 δ 環が余極限・完備化で閉じること（BS 著者版 Remark 2.27）

## 概要
Frobenius に沿う余極限による完全化 A_perf とその普遍性、完全 δ 環の有向余極限・古典的 p 進完備化・導来 (p,d) 完備化 H⁰ が
完全であること。

## 方針
各構成に逆 Frobenius を延ばし、普遍性で両合成が恒等射であることを示す。

## 規約
ここでは BS 著者版 Remark 2.27 の左随伴を扱い、右随伴の逆極限は構成しない。

## 使われ方
prism の完全化（BS 著者版 Lemma 3.9、Prism/Perfection）、André の ω₁ 反復。
-/

@[expose] public noncomputable section
universe u v

/-! ## δ環のFrobenius余極限

任意のδ環をFrobenius持上げの反復で完全化する代数的構成。
Mathlibの環の有向余極限を再利用し、W₂切断を余極限へ移す。
p進完備化・prismのイデアル・perfectoid対応はここでは扱わない。
-/

section DeltaPerfection

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- Frobenius持上げの反復に沿った環の余極限（BS 著者版 Remark 2.27 の左側の完全化の台）。 -/
abbrev DeltaPerfection (D : DeltaStructure p A) :=
  Ring.DirectLimit (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i])

/-- 第n段からδ完全化への標準環射。 -/
def deltaPerfectionOf (D : DeltaStructure p A) (n : ℕ) : A →+* DeltaPerfection D :=
  Ring.DirectLimit.of (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) n

/-- Frobenius反復の像は余極限の遷移で同一視される。 -/
theorem deltaPerfectionOf_iterate (D : DeltaStructure p A) {i j : ℕ} (hij : i ≤ j)
    (x : A) :
    deltaPerfectionOf D j ((D.frobeniusLift : A → A)^[j - i] x) =
      deltaPerfectionOf D i x := by
  exact Ring.DirectLimit.of_f (G := fun _ : ℕ ↦ A)
    (f := fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) hij x

/-- 隣接段のFrobenius像の同一視。 -/
@[simp] theorem deltaPerfectionOf_succ_frobenius (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionOf D (n + 1) (D.frobeniusLift x) = deltaPerfectionOf D n x := by
  simpa using deltaPerfectionOf_iterate D (Nat.le_succ n) x

/-- δ完全化のW₂切断。全段での切断の自然性から余極限上へ延長する。 -/
def deltaPerfectionSection (D : DeltaStructure p A) :
    DeltaPerfection D →+* WittTwo p (DeltaPerfection D) :=
  deltaDirectLimitSection (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x)

/-- 切断は第n段で元の切断と一致する。 -/
@[simp] theorem deltaPerfectionSection_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionSection D (deltaPerfectionOf D n x) =
      wittTwoMap (deltaPerfectionOf D n) (D.sectionHom x) :=
  deltaDirectLimitSection_of (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) n x

/-- Frobenius余極限のδ構造。 -/
def deltaPerfectionStructure (D : DeltaStructure p A) : DeltaStructure p (DeltaPerfection D) :=
  deltaDirectLimitStructure (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x)

/-- 全ての標準段射はδ射。 -/
theorem deltaPerfectionOf_isDeltaHom (D : DeltaStructure p A) (n : ℕ) :
    D.IsDeltaHom (deltaPerfectionStructure D) (deltaPerfectionOf D n) :=
  deltaDirectLimitOf_isDeltaHom (fun _ : ℕ ↦ A)
    (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
    (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) n

/-- 完全化のFrobeniusは各段で元のFrobeniusを適用する。 -/
@[simp] theorem deltaPerfection_frobenius_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    (deltaPerfectionStructure D).frobeniusLift (deltaPerfectionOf D n x) =
      deltaPerfectionOf D n (D.frobeniusLift x) :=
  ((deltaPerfectionOf_isDeltaHom D n).map_frobeniusLift x).symm

/-- 段を一つ進める環射。Frobeniusの逆に相当する。 -/
def deltaPerfectionShift (D : DeltaStructure p A) : DeltaPerfection D →+* DeltaPerfection D :=
  Ring.DirectLimit.lift _ _ _ (fun n ↦ deltaPerfectionOf D (n + 1)) (by
    intro i j hij x
    have h := deltaPerfectionOf_iterate D (Nat.add_le_add_right hij 1) x
    simpa only [Nat.add_sub_add_right] using h)

/-- 段送り射の具体的な式。 -/
@[simp] theorem deltaPerfectionShift_of (D : DeltaStructure p A) (n : ℕ) (x : A) :
    deltaPerfectionShift D (deltaPerfectionOf D n x) = deltaPerfectionOf D (n + 1) x :=
  by
    exact Ring.DirectLimit.lift_of (G := fun _ : ℕ ↦ A)
      (f := fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) _ _ _ n x

/-- 段送り射はFrobeniusの左逆。 -/
theorem deltaPerfectionShift_leftInverse (D : DeltaStructure p A) :
    Function.LeftInverse (deltaPerfectionShift D) (deltaPerfectionStructure D).frobeniusLift := by
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  change deltaPerfectionShift D ((deltaPerfectionStructure D).frobeniusLift
    (deltaPerfectionOf D n a)) = deltaPerfectionOf D n a
  rw [deltaPerfection_frobenius_of, deltaPerfectionShift_of, deltaPerfectionOf_succ_frobenius]

/-- 段送り射はFrobeniusの右逆。 -/
theorem deltaPerfectionShift_rightInverse (D : DeltaStructure p A) :
    Function.RightInverse (deltaPerfectionShift D) (deltaPerfectionStructure D).frobeniusLift := by
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  change (deltaPerfectionStructure D).frobeniusLift
    (deltaPerfectionShift D (deltaPerfectionOf D n a)) = deltaPerfectionOf D n a
  rw [deltaPerfectionShift_of, deltaPerfection_frobenius_of, deltaPerfectionOf_succ_frobenius]

/-- Frobenius余極限は完全δ環（BS 著者版 Remark 2.27 の左側の完全化の完全性）。 -/
theorem deltaPerfection_isPerfect (D : DeltaStructure p A) :
    (deltaPerfectionStructure D).IsPerfect :=
  ⟨(deltaPerfectionShift_leftInverse D).injective,
    (deltaPerfectionShift_rightInverse D).surjective⟩

end SerrePositivity.BhattScholze

end DeltaPerfection

/-! ## δ完全化の普遍性

具体的なFrobenius余極限から任意の完全δ環への基底δ射の一意な延長。
完全化は余極限であり、Mathlibのtiltに使う逆極限Perfectionとは区別する。
-/

section DeltaPerfectionUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B]

/-- 完全δ終域への第n段の射。逆Frobeniusをn回適用する。 -/
def deltaPerfectionStage (E : DeltaStructure p B) (hE : E.IsPerfect) (f : A →+* B) :
    ℕ → A →+* B
  | 0 => f
  | n + 1 => (E.frobeniusEquiv hE).symm.toRingHom.comp (deltaPerfectionStage E hE f n)

/-- 各段の射はδ射。 -/
theorem deltaPerfectionStage_isDeltaHom {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f) (n : ℕ) :
    D.IsDeltaHom E (deltaPerfectionStage E hE f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (E.frobeniusEquiv_symm_isDeltaHom hE).comp ih

/-- 第n+1段の射はFrobenius遷移に沿って第n段の射と一致する。 -/
theorem deltaPerfectionStage_step {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f) (n : ℕ) (x : A) :
    deltaPerfectionStage E hE f (n + 1) (D.frobeniusLift x) =
      deltaPerfectionStage E hE f n x := by
  change (E.frobeniusEquiv hE).symm
    (deltaPerfectionStage E hE f n (D.frobeniusLift x)) = _
  rw [(deltaPerfectionStage_isDeltaHom hE hf n).map_frobeniusLift]
  exact (E.frobeniusEquiv hE).symm_apply_apply _

/-- 全段の射はFrobenius反復遷移と両立する。 -/
theorem deltaPerfectionStage_compatible {D : DeltaStructure p A} {E : DeltaStructure p B}
    (hE : E.IsPerfect) {f : A →+* B} (hf : D.IsDeltaHom E f)
    (i j : ℕ) (hij : i ≤ j) (x : A) :
    deltaPerfectionStage E hE f j ((D.frobeniusLift : A → A)^[j - i] x) =
      deltaPerfectionStage E hE f i x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply', deltaPerfectionStage_step hE hf]
    exact ih

/-- 任意のδ基底射fから完全δ終域への一意な射が、具体的なδ完全化から存在する（BS 著者版 Remark 2.27 の左随伴の普遍性）。 -/
theorem existsUnique_deltaPerfectionHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) (f : A →+* B) (hf : D.IsDeltaHom E f) :
    ∃! g : DeltaPerfection D →+* B,
      (deltaPerfectionStructure D).IsDeltaHom E g ∧ g.comp (deltaPerfectionOf D 0) = f := by
  let g : DeltaPerfection D →+* B := Ring.DirectLimit.lift _ _ B
    (deltaPerfectionStage E hE f) (deltaPerfectionStage_compatible hE hf)
  have hg (n : ℕ) (x : A) : g (deltaPerfectionOf D n x) = deltaPerfectionStage E hE f n x := by
    unfold g deltaPerfectionOf
    rw [Ring.DirectLimit.lift_of]
  have hgd : (deltaPerfectionStructure D).IsDeltaHom E g :=
    deltaDirectLimitLift_isDeltaHom (fun _ : ℕ ↦ A)
      (fun i j _ ↦ (D.frobeniusLift : A → A)^[j - i]) (fun _ ↦ D)
      (fun i j _ x ↦ D.frobeniusLift_iterate_delta (j - i) x) E
      (deltaPerfectionStage E hE f) (deltaPerfectionStage_compatible hE hf)
      (deltaPerfectionStage_isDeltaHom hE hf)
  have hg0 : g.comp (deltaPerfectionOf D 0) = f := by
    ext x
    exact hg 0 x
  refine ⟨g, ⟨hgd, hg0⟩, ?_⟩
  intro l hl
  have hstage (n : ℕ) (x : A) : l (deltaPerfectionOf D n x) = deltaPerfectionStage E hE f n x := by
    induction n with
    | zero => exact DFunLike.congr_fun hl.2 x
    | succ n ih =>
      apply hE.1
      rw [← hl.1.map_frobeniusLift, deltaPerfection_frobenius_of,
        deltaPerfectionOf_succ_frobenius, ih]
      change deltaPerfectionStage E hE f n x =
        (E.frobeniusEquiv hE) ((E.frobeniusEquiv hE).symm (deltaPerfectionStage E hE f n x))
      exact ((E.frobeniusEquiv hE).apply_symm_apply _).symm
  apply RingHom.ext
  intro x
  obtain ⟨n, a, rfl⟩ := Ring.DirectLimit.exists_of x
  exact (hstage n a).trans (hg n a).symm

/-- 完全δ終域へのδ射は、元の環からの第0段の射上の値で決まる。 -/
theorem deltaPerfectionHom_ext (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) (f g : DeltaPerfection D →+* B)
    (hf : (deltaPerfectionStructure D).IsDeltaHom E f)
    (hg : (deltaPerfectionStructure D).IsDeltaHom E g)
    (hfg : f.comp (deltaPerfectionOf D 0) = g.comp (deltaPerfectionOf D 0)) : f = g := by
  obtain ⟨_, _, hu⟩ := existsUnique_deltaPerfectionHom D E hE
    (g.comp (deltaPerfectionOf D 0)) (hg.comp (deltaPerfectionOf_isDeltaHom D 0))
  exact (hu f ⟨hf, hfg⟩).trans (hu g ⟨hg, rfl⟩).symm

end SerrePositivity.BhattScholze

end DeltaPerfectionUniversal

/-! ## 完全 δ 環の余極限の完全性

BS 著者版 Lemma 3.9（著者版 pp.31–32）および BS 著者版 Theorem 7.14（p.61）の極限操作に用いる。
既存の任意図式の δ 余極限構造について、各段の Frobenius 同型を余極限へ移す。
-/

section PerfectDeltaColimit

open SerrePositivity.BhattScholze
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι]
    (A : ι → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (D : ∀ i, DeltaStructure p (A i))
    (hδ : ∀ i j h, (D i).IsDeltaHom (D j) (f i j h))
/-- ## 概要
完全 δ 環と δ 遷移射からなる図式の環余極限上の標準 δ 構造は完全である。
BS 著者版 Lemma 3.9（著者版 pp.31–32）、BS 著者版 Theorem 7.14（p.61）の極限段に用いる補助命題。

## 方針
各段の Frobenius 環同型の両立性から余極限上の環同型を作り、
標準段射上でその同型が余極限の Frobenius 持上げそのものであることを示す。

## 規約
添字の有向性・非空性、遷移射の単射性、p 正則性を追加仮定としない。
既存の deltaDirectLimitStructure を使い、別の δ 構造は定義しない。

## 使われ方
perfectoid 塔の Fontaine 環の未完備余極限を完全 δ 環として扱う。
-/
theorem deltaDirectLimit_isPerfect (hD : ∀ i, (D i).IsPerfect) :
    (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D (fun i j h x ↦ hδ i j h x)).IsPerfect := by
  let E := fun i ↦ (D i).frobeniusEquiv (hD i)
  have hc : ∀ i j h, (E j).toRingHom.comp (f i j h) = (f i j h).comp (E i) := by
    intro i j h
    ext x
    exact ((hδ i j h).map_frobeniusLift x).symm
  let e := Ring.DirectLimit.congr E hc
  have he : (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x)).frobeniusLift = e.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change (deltaDirectLimitStructure A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x)).frobeniusLift (Ring.DirectLimit.of A (fun i j h ↦ f i j h) i x) =
      e (Ring.DirectLimit.of A (fun i j h ↦ f i j h) i x)
    rw [Ring.DirectLimit.congr_apply_of]
    exact ((deltaDirectLimitOf_isDeltaHom A (fun i j h ↦ f i j h) D
      (fun i j h x ↦ hδ i j h x) i).map_frobeniusLift x).symm
  change Function.Bijective _
  rw [he]
  exact e.bijective
end SerrePositivity.BhattScholze.Andre.Transfinite

end PerfectDeltaColimit

/-! ## 完全δ環の古典的p進完備化

BS 著者版 Lemma 3.9のp進完備化段階に使うδ環の定理。
逆Frobeniusを古典的完備化に延長し、射の外延性で両逆の等式を証明する。
導来完備化との比較やprismのイデアルの処理は含めない。
-/

section PerfectDeltaPCompletion

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環を古典的p進完備化しても完全δ環となる。 -/
theorem IsPerfect.adicCompletion_span_p {D : DeltaStructure p A} (hD : D.IsPerfect) :
    (D.adicCompletion (Ideal.span {(p : A)}) (Ideal.subset_span (by simp))).IsPerfect := by
  let I : Ideal A := Ideal.span {(p : A)}
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have hp : (p : A) ∈ I := Ideal.subset_span (by simp)
  let C := AdicCompletion I A
  let j := algebraMap A C
  let J : Ideal C := Ideal.span {(p : C)}
  let DC := D.adicCompletion I hp
  have hJ : I.map j = J := by simp [I, J, Ideal.map_span, j]
  let : IsAdicComplete I C := AdicCompletion.isAdicComplete hI
  let : IsAdicComplete J C := by
    rw [← hJ]
    exact (IsAdicComplete.map_algebraMap_iff (I := I) (S := C) (M := C)).mpr inferInstance
  let ψ := (D.frobeniusEquiv hD).symm.toRingHom
  have hδj := D.isDeltaHom_adicCompletion I hp
  have hψ : D.IsDeltaHom D ψ := D.frobeniusEquiv_symm_isDeltaHom hD
  have hIJ : I.map (j.comp ψ) ≤ J := by
    simp [I, J, Ideal.map_span]
  obtain ⟨g, hg, _⟩ := D.existsUnique_adicCompletion_lift DC I hp hI J
    (j.comp ψ) (hδj.comp hψ) hIJ
  have hgj (r : A) : g (j r) = j (ψ r) := DFunLike.congr_fun hg.1 r
  have hFj (r : A) : DC.frobeniusLift (j r) = j (D.frobeniusLift r) :=
    (hδj.map_frobeniusLift r).symm
  have hbase : I.map j ≤ J := hJ.le
  have hFG : DC.frobeniusLift.comp g = RingHom.id C := by
    apply adicCompletion_extension_unique I hI J j hbase
    · apply RingHom.ext
      intro r
      change DC.frobeniusLift (g (j r)) = j r
      rw [hgj, hFj]
      change j ((D.frobeniusEquiv hD) ((D.frobeniusEquiv hD).symm r)) = j r
      rw [RingEquiv.apply_symm_apply]
    · rfl
  have hGF : g.comp DC.frobeniusLift = RingHom.id C := by
    apply adicCompletion_extension_unique I hI J j hbase
    · apply RingHom.ext
      intro r
      change g (DC.frobeniusLift (j r)) = j r
      rw [hFj, hgj]
      change j ((D.frobeniusEquiv hD).symm ((D.frobeniusEquiv hD) r)) = j r
      rw [RingEquiv.symm_apply_apply]
    · rfl
  have hleft : Function.LeftInverse g DC.frobeniusLift := fun x ↦ DFunLike.congr_fun hGF x
  have hright : Function.RightInverse g DC.frobeniusLift := fun x ↦ DFunLike.congr_fun hFG x
  exact ⟨hleft.injective, hright.surjective⟩

end SerrePositivity.BhattScholze.DeltaStructure

end PerfectDeltaPCompletion

/-! ## 完全δ環の実導来(p,d)完備化の完全性

BS 著者版 Lemma 3.9の完全化後の計算。
逆Frobeniusを実H⁰へ延長し、両合成を環普遍性から恒等射と判定する。
-/

section PerfectDeltaPDCompletion

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環の実(p,d)完備化H⁰のδ構造は完全。源の古典的完備性は不要。 -/
theorem deltaPDCompletionStructure_isPerfect (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionStructure D d).IsPerfect := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let DH := deltaPDCompletionStructure D d
  let j := pdCompletionUnit A p d
  let e := D.frobeniusEquiv hD
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  have hj := pdCompletionUnit_isDeltaHom D d
  let f : A →+* H := j.comp e.symm.toRingHom
  have hf : D.IsDeltaHom DH f := hj.comp (D.frobeniusEquiv_symm_isDeltaHom hD)
  have hd' : IsModuleComplete H (f d) (ModuleCat.of H H) := by
    apply deltaImage_isModuleComplete_of_frobenius D j (e.symm d) hpH
    change IsModuleComplete H (j (e (e.symm d))) (ModuleCat.of H H)
    rw [e.apply_symm_apply]
    exact hdH
  let g := deltaPDCompletionLift D d DH f hf hpH hd'
  have hg : g.comp j = f := deltaPDCompletionLift_comp_unit D d DH f hf hpH hd'
  have hgj (x : A) : g (j x) = j (e.symm x) := RingHom.congr_fun hg x
  have hφj (x : A) : DH.frobeniusLift (j x) = j (e x) := (hj.map_frobeniusLift x).symm
  have hleft : g.comp DH.frobeniusLift = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · apply RingHom.ext
      intro x
      change g (DH.frobeniusLift (j x)) = j x
      rw [hφj, hgj, e.symm_apply_apply]
    · exact RingHom.id_comp j
  have hright : DH.frobeniusLift.comp g = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · apply RingHom.ext
      intro x
      change DH.frobeniusLift (g (j x)) = j x
      rw [hgj, hφj, e.apply_symm_apply]
    · exact RingHom.id_comp j
  have hl : Function.LeftInverse g DH.frobeniusLift := fun x ↦ RingHom.congr_fun hleft x
  have hr : Function.RightInverse g DH.frobeniusLift := fun x ↦ RingHom.congr_fun hright x
  exact ⟨hl.injective, hr.surjective⟩

end SerrePositivity.BhattScholze

end PerfectDeltaPDCompletion

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.27" (partial := special) "左随伴 colim_φ A とその普遍性・完備化での閉性だけ。右随伴 lim_φ A は未。後半の「Frobenius が p ねじれを消す」は Lemma 2.28 の torsion_calculation ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.DeltaPerfection
attribute [cite BS19 "Rem 2.27" (partial := special) "左随伴 colim_φ A とその普遍性・完備化での閉性だけ。右随伴 lim_φ A は未。後半の「Frobenius が p ねじれを消す」は Lemma 2.28 の torsion_calculation ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaPerfection_isPerfect
attribute [cite BS19 "Rem 2.27" (partial := special) "左随伴 colim_φ A とその普遍性・完備化での閉性だけ。右随伴 lim_φ A は未。後半の「Frobenius が p ねじれを消す」は Lemma 2.28 の torsion_calculation ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_deltaPerfectionHom
