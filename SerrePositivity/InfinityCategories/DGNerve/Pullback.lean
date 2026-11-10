module
public import SerrePositivity.InfinityCategories.DGNerve.DegeneracyEquation
public import Mathlib.Tactic.CrossRefAttribute

/-! # 任意の単調写像による単体の引き戻し

概要：データの三分岐による引き戻しは常に単体の方程式を満たす。
方針：非単射な写像を基本退化経由に分解し、源の次元について帰納する。
規約：HA Construction 1.3.1.6。使われ方：dg nerve の単体的構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.Simplex

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：任意の単調写像によるデータの引き戻しに一致する単体が存在する。
方針：単射の場合は既存の構成を使い、非単射の場合は基本退化の後の次元の小さい写像に帰着する。
規約：HA Construction 1.3.1.6。使われ方：直接定義する引き戻しに方程式の証明を与える。 -/
lemma exists_pullback {m n : ℕ} (s : Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    ∃ t : Simplex A D m, t.toSimplexData = s.toSimplexData.pullback α := by
  induction m with
  | zero =>
    exact ⟨s.pullbackOfInjective α (fun x y _ => Fin.ext (by omega)), rfl⟩
  | succ m ih =>
    by_cases hi : Function.Injective α
    · exact ⟨s.pullbackOfInjective α hi, rfl⟩
    let θ : ⦋m + 1⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom α
    obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hi
    obtain ⟨t, ht⟩ := ih θ'.toOrderHom
    refine ⟨t.degeneracy i, ?_⟩
    change t.toSimplexData.pullback i.predAboveOrderHom = s.toSimplexData.pullback α
    rw [ht, SimplexData.pullback_comp]
    congr 1
    have h := congrArg SimplexCategory.Hom.toOrderHom hθ
    simpa only [θ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
      SimplexCategory.comp_toOrderHom, SimplexCategory.σ] using h.symm

/-- 概要：任意の単調写像に沿って dg nerve の単体を引き戻せる。
方針：データ部分は指定された三分岐のまま取り、存在補題から方程式だけを得る。
規約：HA Construction 1.3.1.6。使われ方：`dgNerve.map` の単体的構造。 -/
@[kerodon 00PQ]
def pullback {m n : ℕ} (s : Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) : Simplex A D m where
  toSimplexData := s.toSimplexData.pullback α
  equation := by
    obtain ⟨t, ht⟩ := s.exists_pullback α
    rw [← ht]
    exact t.equation

/-- 概要：引き戻しのデータは三分岐のデータの引き戻しと定義上一致する。
方針：定義の評価。規約：HA Construction 1.3.1.6。
使われ方：面・退化および関手性の計算補題。 -/
lemma pullback_data {m n : ℕ} (s : Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (s.pullback α).toSimplexData = s.toSimplexData.pullback α := rfl

/-- 概要：単体の引き戻しは恒等写像を保つ。
方針：データの等式と単体の外延性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的恒等写像の法則。 -/
lemma pullback_id {n : ℕ} (s : Simplex A D n) : s.pullback OrderHom.id = s :=
  Simplex.ext (SimplexData.pullback_id s.toSimplexData)

/-- 概要：単体の引き戻しは合成に対して反変。
方針：データの合成の法則と単体の外延性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的合成の法則。 -/
lemma pullback_comp {l m n : ℕ} (s : Simplex A D n)
    (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1)) :
    (s.pullback β).pullback α = s.pullback (β.comp α) :=
  Simplex.ext (SimplexData.pullback_comp s.toSimplexData α β)

end SerrePositivity.InfinityCategories.DGNerve.Simplex
