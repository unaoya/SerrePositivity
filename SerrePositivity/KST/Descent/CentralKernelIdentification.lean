module

public import SerrePositivity.KST.Descent.CentralSupportCriterion
public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# 中心局所化の共通核と既存の台つき部分圏の同定

## 概要
各中心局所化で零になる対象の充満部分圏を、既存の scalarSupported の部分圏と同定する。

## 方針
自己準同型の局所化比較から各対象の台条件の同値を証明し、恒等関手を両部分圏へ制限する。

## 規約
局所化比較の実現は T2 の入力であり、TT 局所化や (3.6) 全体の同定は別に残る。

## 使われ方
論文 (3.6) の compact kernel と中心台を持つ perfect 対象の比較。TT Theorem 7.4 への接続。
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {R : Type r} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {ι : Type*} {E : ι → Type w} [∀ i, Category.{t} (E i)]
  [∀ i, Preadditive (E i)] [∀ i, Linear R (E i)]
  (loc : ∀ i, C ⥤ E i)

/-- 概要：各指定中心局所化で零になる対象の共通核（論文 (3.6)）。
方針：元の圏の対象に各局所化での零性を課す。
規約：局所化先の圏は生成元ごとに異なってよい。
使われ方：中心台を持つ対象の既存の部分圏との比較。 -/
def centralLocalizationKernel : ObjectProperty C := fun P ↦ ∀ i, IsZero ((loc i).obj P)

variable [Finite ι] (z : ι → R) [∀ i, (loc i).Additive] [∀ i, (loc i).Linear R]
  [∀ i (P : C), IsLocalizedModule (Submonoid.powers (z i))
    ((loc i).mapLinearMap R : (P ⟶ P) →ₗ[R] _)]

/-- 概要：中心局所化の共通核は既存の正指数の台条件と一致（論文 (3.6)）。
方針：有限生成系の台判定から得た共通指数を一つ増やし、既存の正指数の規約へ合わせる。
規約：比較の存在を公理に置き換えず、IsLocalizedModule の明示的な入力を使う。
使われ方：既存の scalarSupported の三角圏・K₀ の資産への接続。 -/
theorem centralLocalizationKernel_iff_scalarSupported (P : C) :
    centralLocalizationKernel loc P ↔ scalarSupported z P := by
  rw [centralLocalizationKernel, centralSupport_iff_power_annihilation P z loc]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.zero_lt_succ n, fun i ↦
      central_power_kills_id_mono (z i) P (Nat.le_succ n) (hn i)⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

/-- 概要：二つの台条件は対象の述語として等しい（論文 (3.6)）。
方針：各対象での同値を外延性へ渡す。
規約：対象や射を置き換えない。使われ方：既存の台つき部分圏の構造の移送。 -/
theorem centralLocalizationKernel_eq_scalarSupported :
    centralLocalizationKernel loc = scalarSupported (C := C) z := by
  funext P
  exact propext (centralLocalizationKernel_iff_scalarSupported loc z P)

/-- 概要：共通局所化核と既存の台つき部分圏の実際の圏同値（論文 (3.6)）。
方針：元の圏の恒等同値を、同じ対象条件を持つ二つの充満部分圏へ制限する。
規約：対象の underlying object と射は同じであり、K 理論の同値は別の界面から得る。
使われ方：TT の compact kernel の記述から既存の支持つき K₀ への接続。 -/
noncomputable def centralKernelScalarEquivalence :
    (centralLocalizationKernel loc).FullSubcategory ≌
      (scalarSupported (C := C) z).FullSubcategory :=
  (CategoryTheory.Equivalence.refl : C ≌ C).congrFullSubcategory (by
    funext P
    exact propext (centralLocalizationKernel_iff_scalarSupported loc z P).symm)

/-- 概要：部分圏同値の順方向は元の圏への忘却と可換（論文 (3.6)）。
方針：各対象の恒等同型を使う。
規約：underlying object と射を保持する。使われ方：K0・T2 の比較の指定写像との整合性。 -/
noncomputable def centralKernelScalarEquivalence_forget :
    (centralKernelScalarEquivalence loc z).functor ⋙ (scalarSupported (C := C) z).ι ≅
      (centralLocalizationKernel loc).ι :=
  NatIso.ofComponents (fun P ↦ Iso.refl P.obj) (by
    intro P Q f
    change f.hom ≫ 𝟙 Q.obj = 𝟙 P.obj ≫ f.hom
    simp)

/-- 概要：部分圏同値の逆方向も元の圏への忘却と可換（論文 (3.6)）。
方針：各対象の恒等同型を使う。
規約：二方向の比較を同じ元の圏へ戻す。使われ方：台の同定の自然性。 -/
noncomputable def centralKernelScalarEquivalence_inverse_forget :
    (centralKernelScalarEquivalence loc z).inverse ⋙ (centralLocalizationKernel loc).ι ≅
      (scalarSupported (C := C) z).ι :=
  NatIso.ofComponents (fun P ↦ Iso.refl P.obj) (by
    intro P Q f
    change f.hom ≫ 𝟙 Q.obj = 𝟙 P.obj ≫ f.hom
    simp)

/-- 概要：台の同定の順方向は加法的（論文 (3.6)）。
方針：恒等関手の充満部分圏への制限を使う。
規約：射の加法は元の圏の加法。使われ方：支持つき K₀ の比較。 -/
instance centralKernelScalarEquivalence_functor_additive :
    (centralKernelScalarEquivalence loc z).functor.Additive := by
  dsimp [centralKernelScalarEquivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

/-- 概要：台の同定の順方向は中心 R 線形（論文 (3.6)）。
方針：恒等関手の充満部分圏への制限を使う。
規約：中心作用を保つ。使われ方：係数つき局所化との整合性。 -/
instance centralKernelScalarEquivalence_functor_linear :
    (centralKernelScalarEquivalence loc z).functor.Linear R where
  map_smul _ _ := rfl

/-- 概要：台の同定の逆方向も加法的（論文 (3.6)）。
方針：恒等関手の充満部分圏への制限を使う。
規約：射の加法を保持する。使われ方：支持つき K₀ の逆比較。 -/
instance centralKernelScalarEquivalence_inverse_additive :
    (centralKernelScalarEquivalence loc z).inverse.Additive := by
  dsimp [centralKernelScalarEquivalence, CategoryTheory.Equivalence.congrFullSubcategory]
  infer_instance

/-- 概要：台の同定の逆方向も中心 R 線形（論文 (3.6)）。
方針：恒等関手の充満部分圏への制限を使う。
規約：中心作用を保持する。使われ方：二方向の係数比較。 -/
instance centralKernelScalarEquivalence_inverse_linear :
    (centralKernelScalarEquivalence loc z).inverse.Linear R where
  map_smul _ _ := rfl

end SerrePositivity.KST.Descent
