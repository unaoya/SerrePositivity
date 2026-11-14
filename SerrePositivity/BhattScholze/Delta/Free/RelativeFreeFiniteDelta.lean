module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Algebra.MvPolynomial.Equiv
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Logic.Function.Iterate

/-!
# 相対自由 δ 環の有限段での δ の計算

## 概要
R[x_(s,n)] を初期 N+1 段と後続に分け、δ を「初期 N+1 段の多項式 → 初期 N+2 段の多項式」の写像として計算する。
加法・乗法・Frobenius の公式、イデアル冪の評価、反復。
BS 著者版 Lemma 2.11 と Remark 2.14 の相対自由 δ 座標を有限段で扱う。

## 方針
W₂ への有限段の計算射を相対自由 δ 環の切断と比較する。有限段そのものに δ 構造は与えない。

## 規約
基底の p ねじれを許す。

## 使われ方
André の一段の拡大の関係式計算（Division/Relations）、Witt 座標（Free/RelativeFreeWitt）。
-/

@[expose] public noncomputable section
universe u v

/-! ## 相対自由変数の任意有限初期段と後続段の分離

初期N段を係数多項式へ、残りを外側多項式へ送る標準同型。
N=0と任意添字を含み、δ構造の保存や平坦性はこの同型だけから主張しない。
-/

section RelativeFreeFiniteVariableSplit

namespace SerrePositivity.BhattScholze
variable (N : ℕ) (σ : Type u) (A : Type v) [CommRing A]

/-- 初期N段と残りを分け、後続段の番号をNだけ繰り下げる添字同値。 -/
def relativeFreeFiniteVariableSplit : σ × ℕ ≃ (σ × ℕ) ⊕ (σ × Fin N) where
  toFun z := if h : z.2 < N then Sum.inr (z.1, ⟨z.2, h⟩) else Sum.inl (z.1, z.2 - N)
  invFun z := match z with
    | Sum.inl (s, n) => (s, n + N)
    | Sum.inr (s, i) => (s, i.val)
  left_inv z := by
    obtain ⟨s, n⟩ := z
    by_cases hn : n < N
    · simp [hn]
    · simp [hn, Nat.sub_add_cancel (by omega : N ≤ n)]
  right_inv z := by
    cases z with
    | inl z =>
        obtain ⟨s, n⟩ := z
        simp [show ¬n + N < N by omega]
    | inr z =>
        obtain ⟨s, i⟩ := z
        simp [i.isLt]

/-- 初期N段の添字は係数側へ送られる。 -/
@[simp] theorem relativeFreeFiniteVariableSplit_initial (s : σ) (i : Fin N) :
    relativeFreeFiniteVariableSplit N σ (s, i.val) = Sum.inr (s, i) := by
  simp [relativeFreeFiniteVariableSplit, i.isLt]

/-- 後続段の添字は外側へ送られる。 -/
@[simp] theorem relativeFreeFiniteVariableSplit_tail (s : σ) (n : ℕ) :
    relativeFreeFiniteVariableSplit N σ (s, n + N) = Sum.inl (s, n) := by
  simp [relativeFreeFiniteVariableSplit, show ¬n + N < N by omega]

/-- 相対自由環を、初期N段の係数多項式環上の後続多項式環へ分離する。 -/
def relativeFreeFiniteVariableSplitAlgEquiv :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A]
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin N) A) :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteVariableSplit N σ)).trans
    (MvPolynomial.sumAlgEquiv A (σ × ℕ) (σ × Fin N))

/-- 分離同型は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_C (a : A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 初期N段の変数は係数多項式の変数となる。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_X_initial (s : σ) (i : Fin N) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, i.val)) =
      MvPolynomial.C (MvPolynomial.X (s, i)) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 後続変数は外側の変数となる。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_X_tail (s : σ) (n : ℕ) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, n + N)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 有限初期段の変数を元の相対自由環へ含める標準射。 -/
def relativeFreeFiniteInitialPolynomialMap :
    MvPolynomial (σ × Fin N) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2.val))

/-- 後続変数を元の相対自由環へ含める標準射。 -/
def relativeFreeFiniteTailPolynomialMap :
    MvPolynomial (σ × ℕ) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2 + N))

/-- 任意の有限初期多項式の包含は、分離後の係数射となる。 -/
theorem relativeFreeFiniteVariableSplitAlgEquiv_initial (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (relativeFreeFiniteInitialPolynomialMap N σ A f) =
      MvPolynomial.C f := by
  have he : (relativeFreeFiniteVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteInitialPolynomialMap N σ A).toRingHom =
      (MvPolynomial.C : MvPolynomial (σ × Fin N) A →+*
        MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin N) A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteInitialPolynomialMap]
    · intro z
      obtain ⟨s, i⟩ := z
      simp [relativeFreeFiniteInitialPolynomialMap]
  exact RingHom.congr_fun he f

/-- 任意の後続多項式の包含は、分離後の係数包含による写像となる。 -/
theorem relativeFreeFiniteVariableSplitAlgEquiv_tail (f : MvPolynomial (σ × ℕ) A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (relativeFreeFiniteTailPolynomialMap N σ A f) =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial (σ × Fin N) A) f := by
  have he : (relativeFreeFiniteVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteTailPolynomialMap N σ A).toRingHom =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial (σ × Fin N) A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteTailPolynomialMap]
    · intro z
      obtain ⟨s, n⟩ := z
      simp [relativeFreeFiniteTailPolynomialMap]
  exact RingHom.congr_fun he f

/-- 逆同型は二重の係数を元の係数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_C_C (a : A) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

/-- 逆同型は係数側変数を初期段の変数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_C_X (s : σ) (i : Fin N) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.C (MvPolynomial.X (s, i))) =
      MvPolynomial.X (s, i.val) := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

/-- 逆同型は外側変数をN以降の変数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_X (s : σ) (n : ℕ) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + N) := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

end SerrePositivity.BhattScholze

end RelativeFreeFiniteVariableSplit

/-! ## 相対自由δ計算の有限段表示

初期N+1段の多項式のδ像を初期N+2段で計算する。
同じ有限段にδ構造を与えることは要求しない。
-/

section RelativeFreeFiniteDeltaStep

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限変数を次の有限段へ含める標準多項式射。 -/
def relativeFreeFiniteStepInclusion :
    MvPolynomial (σ × Fin (N + 1)) A →+* MvPolynomial (σ × Fin (N + 2)) A :=
  (MvPolynomial.rename fun z => (z.1, z.2.castSucc)).toRingHom

/-- 有限初期変数の標準包含は単射。零係数環も含む。 -/
theorem relativeFreeFiniteInitialPolynomialMap_injective :
    Function.Injective (relativeFreeFiniteInitialPolynomialMap N σ A) := by
  apply MvPolynomial.rename_injective
  intro x y h
  exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
    (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))

/-- 一段大きい有限多項式環へのW₂計算射。 -/
def relativeFreeFiniteDeltaStepSection (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* WittTwo p (MvPolynomial (σ × Fin (N + 2)) A) :=
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun z => TruncatedWittVector.mk p (fun i => if i = 0 then
      MvPolynomial.X (z.1, z.2.castSucc) else MvPolynomial.X (z.1, z.2.succ)))

/-- W₂計算射の係数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteDeltaStepSection N σ D (MvPolynomial.C a) =
      wittTwoMap (p := p) MvPolynomial.C (D.sectionHom a) := by
  exact MvPolynomial.eval₂Hom_C _ _ a

/-- W₂計算射の変数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_X (D : DeltaStructure p A)
    (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaStepSection N σ D (MvPolynomial.X (s, i)) =
      TruncatedWittVector.mk p (fun j => if j = 0 then
        MvPolynomial.X (s, i.castSucc) else MvPolynomial.X (s, i.succ)) := by
  exact MvPolynomial.eval₂Hom_X' _ _ (s, i)

/-- 第0座標は次の有限段への標準包含。 -/
theorem relativeFreeFiniteDeltaStepSection_projection (D : DeltaStructure p A) :
    (wittTwoProjection p (MvPolynomial (σ × Fin (N + 2)) A)).comp
      (relativeFreeFiniteDeltaStepSection N σ D) = relativeFreeFiniteStepInclusion N σ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, relativeFreeFiniteDeltaStepSection_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    simp [relativeFreeFiniteStepInclusion]
  · intro z
    obtain ⟨s, i⟩ := z
    simp [relativeFreeFiniteDeltaStepSection_X, relativeFreeFiniteStepInclusion]

/-- 第1座標として一段大きい有限環で計算したδ像。 -/
def relativeFreeFiniteDeltaStep (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : MvPolynomial (σ × Fin (N + 2)) A :=
  (relativeFreeFiniteDeltaStepSection N σ D f).coeff 1

/-- 有限δ計算の係数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C a) = MvPolynomial.C (D.delta a) := by
  simp only [relativeFreeFiniteDeltaStep, relativeFreeFiniteDeltaStepSection_C, wittTwoMap_coeff]
  rfl

/-- 有限δ計算の変数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_X (D : DeltaStructure p A)
    (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.X (s, i)) = MvPolynomial.X (s, i.succ) := by
  simp [relativeFreeFiniteDeltaStep]

/-- 有限W₂計算と元の相対自由W₂切断の可換図式。 -/
theorem relativeFreeFiniteDeltaStepSection_naturality (D : DeltaStructure p A) :
    (wittTwoMap (p := p) (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom).comp
      (relativeFreeFiniteDeltaStepSection N σ D) =
      (relativeFreeDeltaSection σ D).comp
        (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    apply TruncatedWittVector.ext
    intro i
    simp [relativeFreeFiniteDeltaStepSection_C, relativeFreeFiniteInitialPolynomialMap,
      relativeFreeDeltaSection, wittTwoMap_coeff]
  · intro z
    obtain ⟨s, i⟩ := z
    apply TruncatedWittVector.ext
    intro j
    fin_cases j <;>
      simp [relativeFreeFiniteDeltaStepSection_X, relativeFreeFiniteInitialPolynomialMap,
        relativeFreeDeltaSection, wittTwoMap_coeff]

/-- 任意有限初期多項式の実際のδ像は、次の有限初期段の多項式で表せる。 -/
theorem relativeFreeFiniteDeltaStep_delta_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeDeltaStructure σ D).delta
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) =
      relativeFreeFiniteInitialPolynomialMap (N + 2) σ A (relativeFreeFiniteDeltaStep N σ D f) := by
  have h := congrArg (fun z : WittTwo p (RelativeFreeDeltaRing (R := A) σ) => z.coeff 1)
    (RingHom.congr_fun (relativeFreeFiniteDeltaStepSection_naturality N σ D) f)
  simp only [RingHom.comp_apply, wittTwoMap_coeff] at h
  exact h.symm

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaStep

/-! ## 有限次段の最高変数と初期変数の分離

最高段を外側変数、初期段を係数多項式へ送る標準同型。
-/

section RelativeFreeFiniteTopVariableSplit

namespace SerrePositivity.BhattScholze
variable (N : ℕ) (σ : Type u) (A : Type v) [CommRing A]

/-- 次の有限段の最高変数を左項へ分ける添字同値。 -/
def relativeFreeFiniteTopVariableSplit : σ × Fin (N + 2) ≃ σ ⊕ (σ × Fin (N + 1)) where
  toFun z := if h : z.2.val < N + 1 then Sum.inr (z.1, ⟨z.2.val, h⟩) else Sum.inl z.1
  invFun z := match z with
    | Sum.inl s => (s, Fin.last (N + 1))
    | Sum.inr (s, i) => (s, i.castSucc)
  left_inv z := by
    obtain ⟨s, i⟩ := z
    by_cases hi : i.val < N + 1
    · simp [hi]
    · simp only [dite_eq_right hi, Prod.mk.injEq, true_and]
      apply Fin.ext
      have hn := i.isLt
      simp only [Fin.val_last]
      omega
  right_inv z := by
    cases z with
    | inl s => simp
    | inr z =>
        obtain ⟨s, i⟩ := z
        simp [i.isLt]

/-- 最高変数の添字は外側へ送られる。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplit_top (s : σ) :
    relativeFreeFiniteTopVariableSplit N σ (s, Fin.last (N + 1)) = Sum.inl s := by
  simp [relativeFreeFiniteTopVariableSplit]

/-- 初期変数の添字は係数側へ送られる。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplit_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopVariableSplit N σ (s, i.castSucc) = Sum.inr (s, i) := by
  have hi : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp [relativeFreeFiniteTopVariableSplit, hi]

/-- 有限次段は、初期有限変数の係数多項式環上の最高変数の多項式環。 -/
def relativeFreeFiniteTopVariableSplitAlgEquiv :
    MvPolynomial (σ × Fin (N + 2)) A ≃ₐ[A]
      MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A) :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteTopVariableSplit N σ)).trans
    (MvPolynomial.sumAlgEquiv A σ (σ × Fin (N + 1)))

/-- 最高変数分離の係数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_C (a : A) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 最高変数分離の最高変数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_X_top (s : σ) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, Fin.last (N + 1))) =
      MvPolynomial.X s := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 最高変数分離の初期変数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_X_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, i.castSucc)) =
      MvPolynomial.C (MvPolynomial.X (s, i)) := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 次段への標準包含は、最高変数分離後の係数射となる。 -/
theorem relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C f := by
  have he : (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteStepInclusion N σ) =
      (MvPolynomial.C : MvPolynomial (σ × Fin (N + 1)) A →+*
        MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteStepInclusion]
    · intro z
      obtain ⟨s, i⟩ := z
      simp [relativeFreeFiniteStepInclusion]
  exact RingHom.congr_fun he f

end SerrePositivity.BhattScholze

end RelativeFreeFiniteTopVariableSplit

/-! ## 任意有限δ計算の加法・積とFrobenius公式

既存のWitt係数公式を有限W₂計算射へ適用する。
-/

section RelativeFreeFiniteDeltaStepIdentities

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 有限包含の合成は元の相対自由環への標準包含。 -/
theorem relativeFreeFiniteStepInclusion_comp_initial :
    (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom.comp
      (relativeFreeFiniteStepInclusion (A := A) N σ) =
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [relativeFreeFiniteInitialPolynomialMap, relativeFreeFiniteStepInclusion]
  · intro z
    obtain ⟨s, i⟩ := z
    simp [relativeFreeFiniteInitialPolynomialMap, relativeFreeFiniteStepInclusion]

/-- 有限計算射の第0座標の点ごとの式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_coeff_zero (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteDeltaStepSection N σ D f).coeff 0 = relativeFreeFiniteStepInclusion N σ f :=
  RingHom.congr_fun (relativeFreeFiniteDeltaStepSection_projection N σ D) f

/-- 有限δ計算は零を零へ送る。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_zero (D : DeltaStructure p A) :
    relativeFreeFiniteDeltaStep N σ D 0 = 0 := by
  change (relativeFreeFiniteDeltaStepSection N σ D 0).coeff 1 = 0
  rw [map_zero]
  change (0 : WittVector p (MvPolynomial (σ × Fin (N + 2)) A)).coeff 1 = 0
  exact WittVector.zero_coeff (R := MvPolynomial (σ × Fin (N + 2)) A) p 1

/-- 有限δ計算は単位元を零へ送る。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_one (D : DeltaStructure p A) :
    relativeFreeFiniteDeltaStep N σ D 1 = 0 := by
  change (relativeFreeFiniteDeltaStepSection N σ D 1).coeff 1 = 0
  rw [map_one]
  change (1 : WittVector p (MvPolynomial (σ × Fin (N + 2)) A)).coeff 1 = 0
  exact WittVector.one_coeff_eq_of_pos p _ 1 (by decide)

/-- 任意有限段のδ加法公式。補正項の入力は次の段への標準包含。 -/
theorem relativeFreeFiniteDeltaStep_add (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (f + g) =
      relativeFreeFiniteDeltaStep N σ D f + relativeFreeFiniteDeltaStep N σ D g +
        (WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
          WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ g)).coeff 1 := by
  change (relativeFreeFiniteDeltaStepSection N σ D (f + g)).coeff 1 = _
  rw [map_add]
  change ((relativeFreeFiniteDeltaStepSection N σ D f).out +
    (relativeFreeFiniteDeltaStepSection N σ D g).out).coeff 1 = _
  rw [witt_add_coeff_one]
  simp [TruncatedWittVector.out, relativeFreeFiniteDeltaStep]

/-- 任意有限段のδ積公式。pねじれの除去は使わない。 -/
theorem relativeFreeFiniteDeltaStep_mul (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (f * g) =
      (relativeFreeFiniteStepInclusion N σ f) ^ p * relativeFreeFiniteDeltaStep N σ D g +
        relativeFreeFiniteDeltaStep N σ D f * (relativeFreeFiniteStepInclusion N σ g) ^ p +
        (p : MvPolynomial (σ × Fin (N + 2)) A) *
          relativeFreeFiniteDeltaStep N σ D f * relativeFreeFiniteDeltaStep N σ D g := by
  change (relativeFreeFiniteDeltaStepSection N σ D (f * g)).coeff 1 = _
  rw [map_mul]
  change ((relativeFreeFiniteDeltaStepSection N σ D f).out *
    (relativeFreeFiniteDeltaStepSection N σ D g).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, relativeFreeFiniteDeltaStep]

/-- 有限W₂計算射から得る一段大きい環へのFrobenius射。 -/
def relativeFreeFiniteFrobeniusStep (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* MvPolynomial (σ × Fin (N + 2)) A :=
  (wittTwoFrobenius p (MvPolynomial (σ × Fin (N + 2)) A)).comp
    (relativeFreeFiniteDeltaStepSection N σ D)

/-- 有限Frobenius射の具体的な式。 -/
@[simp] theorem relativeFreeFiniteFrobeniusStep_apply (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteFrobeniusStep N σ D f = (relativeFreeFiniteStepInclusion N σ f) ^ p +
      (p : MvPolynomial (σ × Fin (N + 2)) A) * relativeFreeFiniteDeltaStep N σ D f := by
  simp [relativeFreeFiniteFrobeniusStep, relativeFreeFiniteDeltaStep]

/-- 有限Frobenius計算の像は、相対自由δ環の実際のFrobenius像。 -/
theorem relativeFreeFiniteFrobeniusStep_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteInitialPolynomialMap (N + 2) σ A (relativeFreeFiniteFrobeniusStep N σ D f) =
      (relativeFreeDeltaStructure σ D).frobeniusLift
        (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) := by
  rw [relativeFreeFiniteFrobeniusStep_apply, map_add, map_pow, map_mul, map_natCast,
    ← relativeFreeFiniteDeltaStep_delta_image, DeltaStructure.frobeniusLift_apply]
  have he := RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) N σ) f
  rw [show relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
    (relativeFreeFiniteStepInclusion N σ f) =
      relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f from he]

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaStepIdentities

/-! ## 異なる有限段の間のδ計算のイデアル冪評価

次段イデアルJと初期包含の逆像について、有限δ計算で失う冪を追う。
-/

section RelativeFreeFiniteDeltaAdicEstimate

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 次段のJがpを含むなら、逆像のm+1乗の有限δ像はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : f ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f ∈ J ^ m := by
  exact wittTwoLift_delta_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f hf

/-- 逆像のm+1乗に属す摂動による有限δ像の変化はJのm乗に入る。 -/
theorem relativeFreeFiniteDeltaStep_add_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hg : g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D (f + g) - relativeFreeFiniteDeltaStep N σ D f ∈
      J ^ m := by
  exact wittTwoLift_delta_add_sub_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f g hg

/-- 二代表元が逆像のm+1乗まで一致すれば有限δ像はJのm乗まで一致する。 -/
theorem relativeFreeFiniteDeltaStep_sub_mem_pow (D : DeltaStructure p A)
    (J : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hp : (p : MvPolynomial (σ × Fin (N + 2)) A) ∈ J)
    (m : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : f - g ∈ (J.comap (relativeFreeFiniteStepInclusion N σ)) ^ (m + 1)) :
    relativeFreeFiniteDeltaStep N σ D f - relativeFreeFiniteDeltaStep N σ D g ∈ J ^ m := by
  exact wittTwoLift_delta_sub_mem_pow (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) J hp m f g hfg

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaAdicEstimate

/-! ## 有限δ計算の全反復と誤差冪の損失

初期段を一段ずつ増やし、相対自由δ環の実際の反復と比較する。
-/

section RelativeFreeFiniteDeltaIterate

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限多項式に有限δ計算をk回適用した、具体的な次段多項式。 -/
def relativeFreeFiniteDeltaIterate (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (k : ℕ) → MvPolynomial (σ × Fin (N + k + 1)) A
  | 0 => f
  | k + 1 => relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate D f k)

/-- 零回反復は初期有限多項式。 -/
@[simp] theorem relativeFreeFiniteDeltaIterate_zero (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaIterate N σ D f 0 = f := rfl

/-- 次の反復は一段大きい有限環でのδ計算。 -/
@[simp] theorem relativeFreeFiniteDeltaIterate_succ (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (k : ℕ) :
    relativeFreeFiniteDeltaIterate N σ D f (k + 1) =
      relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate N σ D f k) := rfl

/-- 全反復有限多項式の標準包含像は、実際の相対自由δ環のδ反復。 -/
theorem relativeFreeFiniteDeltaIterate_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (k : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
      (relativeFreeFiniteDeltaIterate N σ D f k) =
        (relativeFreeDeltaStructure σ D).delta^[k]
          (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [relativeFreeFiniteDeltaIterate_succ]
      change relativeFreeFiniteInitialPolynomialMap (N + k + 2) σ A
        (relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate N σ D f k)) = _
      rw [← relativeFreeFiniteDeltaStep_delta_image (N + k) σ D, ih]
      exact (Function.iterate_succ_apply' (relativeFreeDeltaStructure σ D).delta k _).symm

/-- 初期誤差がJ^(m+k)なら、k回の有限δ計算後の包含像の誤差はJ^m。
有限商のδ構造を要求せず、実際の相対自由δ環の冪評価を反復する。 -/
theorem relativeFreeFiniteDeltaIterate_sub_image_mem_pow (D : DeltaStructure p A)
    (J : Ideal (RelativeFreeDeltaRing (R := A) σ))
    (hp : (p : RelativeFreeDeltaRing (R := A) σ) ∈ J)
    (m k : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f -
      relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g ∈ J ^ (m + k)) :
    relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
      (relativeFreeFiniteDeltaIterate N σ D f k) -
        relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
          (relativeFreeFiniteDeltaIterate N σ D g k) ∈ J ^ m := by
  rw [relativeFreeFiniteDeltaIterate_image, relativeFreeFiniteDeltaIterate_image]
  induction k generalizing m with
  | zero => exact hfg
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply (relativeFreeDeltaStructure σ D).delta_sub_mem_pow J hp m
      apply ih (m + 1)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hfg

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaIterate
