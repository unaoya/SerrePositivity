module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.ExactSequence
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.KoszulComparison
public import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison
public import SerrePositivity.CommutativeAlgebra.Adic.FlatTensorFiltration
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public noncomputable section

/-!
# Koszul ホモロジーの pro-消滅

概要：既存の実際の Koszul 冪遷移を最小 pro 形式へ接続する。
方針：Artin–Rees の深い像による零化を使う。
規約：原典の正ホモロジー次数 i は本複体の次数 -i。
使われ方：KST Lemma 4.9・4.10。原典の列長帰納法に対し、ここでは
Artin–Rees と遷移の像の深さによる既存証明を使う。
-/

universe u v

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex
open scoped TensorProduct

/-- 概要：ℕ の反対圏上の図式を最小形式の塔へ移す。
方針：順序射の像を遷移とする。規約：添字の方向は逆。
使われ方：KST §4 の既存 Koszul 逆系の受け入れ。 -/
def Tower.ofInverseDiagram {C : Type u} [Category.{v} C] (F : ℕᵒᵖ ⥤ C) : Tower C where
  obj n := F.obj (Opposite.op n)
  transition h := F.map (homOfLE h).op
  transition_self n := by
    change F.map (𝟙 (Opposite.op n)) = _
    exact F.map_id _
  transition_comp hm hn := by
    rw [← F.map_comp]
    rfl

variable {R : Type u} [CommRing R]

/-- 概要：実際の Koszul 冪複体の塔。方針：既存の冪遷移をそのまま使う。
規約：n 段は座標の n 乗。使われ方：KST Lemma 4.9。 -/
def koszulTower {e : ℕ} (z : Fin e → R) :
    Tower (CochainComplex (ModuleCat.{u} R) ℤ) :=
  Tower.ofInverseDiagram (powerKoszulInverseDiagram z)

/-- 概要：Koszul 冪複体の次数別ホモロジーの塔。
方針：ホモロジー関手で写す。規約：q はコホモロジー次数。
使われ方：KST Lemma 4.9 の pro-零性。 -/
def koszulHomologyTower {e : ℕ} (z : Fin e → R) (q : ℤ) : Tower (ModuleCat.{u} R) :=
  (koszulTower z).map (homologyFunctor _ _ q)

/-- 概要：環係数の正 Koszul ホモロジーは pro-零。
方針：既存の Artin–Rees と遷移深度の証明を最小形式へ移す。
規約：q < 0 は原典の正ホモロジー次数。
使われ方：KST Lemma 4.9、原典の列長帰納法とは異なる Artin–Rees 経路。 -/
theorem koszulHomologyTower_isProZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (q : ℤ) (hq : q < 0) :
    IsProZero (koszulHomologyTower z q) := by
  intro n
  obtain ⟨m, h, hz⟩ := powerKoszul_negative_homology_proZero z q hq n
  exact ⟨m, h, hz⟩

/-- 概要：像のイデアル深度は左テンソルで保たれる。
方針：純テンソルとイデアル倍の生成元について示す。
規約：平坦性は不要。使われ方：KST Lemma 4.9 の有限生成加群係数への拡張。 -/
theorem range_lTensor_le_ideal_smul
    {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (I : Ideal R) (f : N →ₗ[R] P) (hf : LinearMap.range f ≤ I • ⊤) :
    LinearMap.range (f.lTensor M) ≤ (I • ⊤ : Submodule R (M ⊗[R] P)) := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | tmul m n =>
    change m ⊗ₜ[R] f n ∈ _
    have hfn := hf (LinearMap.mem_range_self f n)
    refine Submodule.smul_induction_on hfn ?_ ?_
    · intro r hr x _
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x y hx hy
      simpa [TensorProduct.tmul_add] using Submodule.add_mem _ hx hy

/-- 概要：任意の係数加群をテンソルした Koszul 複体の塔。
方針：元の複体と遷移に同じテンソル関手を施す。
規約：係数加群の有限性・平坦性は定義に不要。使われ方：KST Lemma 4.9。 -/
def koszulTensorTower {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    Tower (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (koszulTower z).map (((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex _)

/-- 概要：係数付き Koszul ホモロジーの塔。
方針：テンソルモデルのホモロジーを取る。
規約：q はコホモロジー次数。使われ方：KST Lemma 4.9 の一般係数。 -/
def koszulTensorHomologyTower {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R)
    (q : ℤ) : Tower (ModuleCat.{u} R) :=
  (koszulTensorTower z M).map (homologyFunctor _ _ q)

/-- 概要：有限生成加群係数の正 Koszul ホモロジーは pro-零。
方針：テンソル後の有限な標的項に Artin–Rees を適用し、冪遷移の像の深さで零化する。
規約：係数加群の平坦性は仮定しない。原典の列長帰納法とは異なる経路。
使われ方：KST Lemma 4.9 の全有限生成加群版。 -/
theorem koszulTensorHomologyTower_isProZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (q : ℤ) (hq : q < 0) : IsProZero (koszulTensorHomologyTower z M q) := by
  intro n
  let L := (koszulTensorTower z M).obj n
  let iso := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
    (koszulTensorConeIso (fun j ↦ z j ^ n) M)
  have hkill : Ideal.span (Set.range (fun j ↦ z j ^ n)) ≤
      Module.annihilator R (L.homology q) := by
    have h := span_le_annihilator_koszulModuleHomology (fun j ↦ z j ^ n) M q
    exact h.trans (iso.hom.hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective iso.hom).mp inferInstance))
  obtain ⟨a, ha⟩ := exists_span_pow_le_powerKoszulIdeal z n
  let : Module.Finite R ((DerivedCompletion.powerKoszulTower R z n).X q) :=
    (koszulComplex_free_finite_X (fun j ↦ z j ^ n) q).2
  have : Module.Finite R (L.X q) :=
    inferInstanceAs (Module.Finite R
      (M ⊗[R] ((DerivedCompletion.powerKoszulTower R z n).X q)))
  obtain ⟨k, hk⟩ := exists_pow_homologyMap_eq_zero_of_deep_image L q
    (Ideal.span (Set.range z)) a (ha.trans hkill)
  refine ⟨n + k, Nat.le_add_right n k, ?_⟩
  apply hk ((koszulTensorTower z M).obj (n + k))
    ((koszulTensorTower z M).transition (Nat.le_add_right n k))
  exact range_lTensor_le_ideal_smul (Ideal.span (Set.range z) ^ k) _
    (powerKoszulInverseDiagram_negative_range_le_span_pow z n k q hq)

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 4.9"] _root_.SerrePositivity.KST.ProExcision.koszulTensorHomologyTower_isProZero
attribute [cite LT "Cor 2.34" (partial := component) "仮定：Noether 環と有限加群の冪 Koszul 塔、別に非正 dg 塔で Tor 比較を入力（Lean が強い）。結論：個別の Koszul 消滅と抽象 Tor 模型からの値のプロ同値。原典の pro-Tor 条件と K のプロ正方形を接続しない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.koszulTensorHomologyTower_isProZero
