module

public import SerrePositivity.KST.ProExcision.TensorBoundary
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 分裂の境界とホモロジー連結写像

概要：次数ごとの分裂から作った境界を短完全列のホモロジー連結写像へ接続する。
方針：サイクルを分裂で持ち上げ、その微分を左項へ戻す代表元計算を使う。
規約：分裂は次数ごとであり、複体射としての切断は要求しない。
使われ方：KST Lemma 4.10 の初頁微分をホモロジーの連結写像から計算する。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：サイクルに分裂境界を作用させると、持ち上げの微分の左項への持ち上げになる。
方針：r≫f=id−g≫s と複体射 g の可換性を使う。
規約：短複体の各次数の分裂だけを入力する。
使われ方：KST Lemma 4.10 のホモロジー連結写像の代表元計算。 -/
theorem splitBoundary_lift_condition
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ)
    {A : ModuleCat.{u} R} (x : A ⟶ S.X₃.X i) (hx : x ≫ S.X₃.d i (i + 1) = 0) :
    x ≫ (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v i (i + 1) rfl ≫
      S.f.f (i + 1) = (x ≫ (σ i).s) ≫ S.X₂.d i (i + 1) := by
  have hxs : (x ≫ (σ i).s) ≫ S.g.f i = x := by
    erw [Category.assoc, (σ i).s_g, Category.comp_id]
  have hz : (x ≫ (σ i).s ≫ S.X₂.d i (i + 1)) ≫ S.g.f (i + 1) = 0 := by
    rw [Category.assoc, Category.assoc, ← S.g.comm]
    rw [← Category.assoc, ← Category.assoc, hxs, hx]
  have hz' : ((x ≫ (σ i).s) ≫ S.X₂.d i (i + 1)) ≫ S.g.f (i + 1) = 0 := by
    simpa only [Category.assoc] using hz
  have hkill : ((x ≫ (σ i).s) ≫ S.X₂.d i (i + 1)) ≫
      S.g.f (i + 1) ≫ (σ (i + 1)).s = 0 := by
    rw [← Category.assoc, hz', zero_comp]
  change x ≫ ((σ i).s ≫ S.X₂.d i (i + 1) ≫ (σ (i + 1)).r) ≫ S.f.f (i + 1) = _
  calc
    _ = (x ≫ (σ i).s ≫ S.X₂.d i (i + 1)) ≫
        ((σ (i + 1)).r ≫ S.f.f (i + 1)) := by simp only [Category.assoc]
    _ = (x ≫ (σ i).s) ≫ S.X₂.d i (i + 1) := by
      erw [(σ (i + 1)).r_f, Preadditive.comp_sub, Category.comp_id]
      erw [hkill, sub_zero]

/-- 概要：サイクルに分裂境界を作用させた結果もサイクル。
方針：左項の単射で比較し、持ち上げの微分の二乗が零であることを使う。
規約：各次数の分裂から単射性を導く。使われ方：KST Lemma 4.10 の連結写像の代表元。 -/
theorem splitBoundary_isCycle
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ)
    {A : ModuleCat.{u} R} (x : A ⟶ S.X₃.X i) (hx : x ≫ S.X₃.d i (i + 1) = 0) :
    (x ≫ (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v i (i + 1) rfl) ≫
      S.X₁.d (i + 1) (i + 1 + 1) = 0 := by
  have : Mono (S.f.f (i + 1 + 1)) := mono_of_mono_fac (σ (i + 1 + 1)).f_r
  rw [← cancel_mono (S.f.f (i + 1 + 1)), zero_comp, Category.assoc, ← S.f.comm,
    ← Category.assoc]
  have h := splitBoundary_lift_condition S σ i x hx
  have hh := congrArg (fun t : A ⟶ S.X₂.X (i + 1) ↦
    t ≫ S.X₂.d (i + 1) (i + 1 + 1)) h
  simpa only [Category.assoc, S.X₂.d_comp_d, comp_zero] using hh

/-- 概要：短完全列のホモロジー連結写像は分裂境界をサイクルに作用させて計算できる。
方針：分裂による持ち上げとその微分に対して Mathlib の連結写像の計算則を適用する。
規約：任意のサイクル射を入力とし、ホモロジー類の代表を固定しない。
使われ方：KST Lemma 4.10 のスペクトル対象の δ と分裂境界の接続。 -/
theorem splitBoundary_connecting
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (hS : S.ShortExact) (i : ℤ)
    {A : ModuleCat.{u} R} (x : A ⟶ S.X₃.X i) (hx : x ≫ S.X₃.d i (i + 1) = 0) :
    S.X₃.liftCycles x (i + 1) (by simp) hx ≫ S.X₃.homologyπ i ≫ hS.δ i (i + 1) rfl =
      S.X₁.liftCycles
        (x ≫ (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v i (i + 1) rfl)
        (i + 1 + 1) (by simp) (splitBoundary_isCycle S σ i x hx) ≫ S.X₁.homologyπ (i + 1) := by
  exact hS.δ_eq i (i + 1) rfl x hx (x ≫ (σ i).s)
    (by erw [Category.assoc, (σ i).s_g, Category.comp_id])
    (x ≫ (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v i (i + 1) rfl)
    (by simpa only [Category.assoc] using splitBoundary_lift_condition S σ i x hx)
    (i + 1 + 1) (by simp)

/-- 概要：分裂境界が誘導するシフトつきホモロジー写像をサイクル上で計算する。
方針：ホモロジー射の自然性とシフトのサイクル比較を使う。
規約：シフト 1 とホモロジー次数 i+1 の比較を明示する。
使われ方：KST Lemma 4.10 の短完全列の連結写像と分裂境界の比較。 -/
theorem splitBoundary_shiftMap_on_cycle
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ)
    {A : ModuleCat.{u} R} (x : A ⟶ S.X₃.X i) (hx : x ≫ S.X₃.d i (i + 1) = 0) :
    S.X₃.liftCycles x (i + 1) (by simp) hx ≫ S.X₃.homologyπ i ≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (CochainComplex.homOfDegreewiseSplit S σ) i (i + 1) (by omega) =
      S.X₁.liftCycles
        (x ≫ (CochainComplex.cocycleOfDegreewiseSplit S σ).1.v i (i + 1) rfl)
        (i + 1 + 1) (by simp) (splitBoundary_isCycle S σ i x hx) ≫ S.X₁.homologyπ (i + 1) := by
  simp only [Functor.shiftMap, CochainComplex.homologyFunctor_shift]
  erw [homologyπ_naturality_assoc, ← Category.assoc, liftCycles_comp_cyclesMap]
  erw [S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ (i + 1) (by omega)
    (i + 1 + 1) (by simp)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  congr 1

/-- 概要：短完全列の連結写像は分裂境界が誘導するシフトつきホモロジー写像と一致する。
方針：全サイクル上の代表元公式を比較し、ホモロジーへの全射で相殺する。
規約：分裂の選択に依存しない連結写像との一致を射として示す。
使われ方：KST Lemma 4.10 のスペクトル対象の δ と明示的な微分の接続。 -/
theorem splitBoundary_connecting_eq_shiftMap
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (hS : S.ShortExact) (i : ℤ) :
    hS.δ i (i + 1) rfl =
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (CochainComplex.homOfDegreewiseSplit S σ) i (i + 1) (by omega) := by
  apply (cancel_epi (S.X₃.homologyπ i)).mp
  have hx := S.X₃.iCycles_d i (i + 1)
  have hl : S.X₃.liftCycles (S.X₃.iCycles i) (i + 1) (by simp) hx =
      𝟙 (S.X₃.cycles i) := by
    rw [← cancel_mono (S.X₃.iCycles i), liftCycles_i, Category.id_comp]
  have h := (splitBoundary_connecting S σ hS i (S.X₃.iCycles i) hx).trans
    (splitBoundary_shiftMap_on_cycle S σ i (S.X₃.iCycles i) hx).symm
  erw [hl, Category.id_comp] at h
  exact h

end SerrePositivity.KST.ProExcision
