module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.IsUniquelyCodimOneFace
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# 一意な非退化面を持つ単体の非退化性

概要：非退化単体が面として一意に現れるなら、対応する高次元単体も非退化である。
方針：退化表示から同じ単体を与える隣接した二つの面を構成する。
規約：Moss 2020 Lemma 29 の補助。非退化面からの単射性により原典の計算を表す。
使われ方：Ex の pairing の対応先の非退化性。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：一意に現れる非退化な面を持つ単体は非退化である。
方針：退化の表示で面との合成が恒等となることから、隣接する二面が等しいと導く。
規約：Moss 2020 Lemma 29 の一般的な補助。
使われ方：proper pairing の非退化性の検証。
-/
theorem nonDegenerate_of_unique_face (X : SSet.{u}) (n : ℕ)
    (x : X _⦋n⦌) (y : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate n)
    (hxy : ∃! i : Fin (n + 2), X.δ i y = x) : y ∈ X.nonDegenerate (n + 1) := by
  rw [X.mem_nonDegenerate_iff_notMem_degenerate]
  intro hy
  rw [X.degenerate_eq_iUnion_range_σ] at hy
  obtain ⟨h, t, rfl⟩ := Set.mem_iUnion.mp hy
  obtain ⟨i, hi, hu⟩ := hxy
  change (X.map (SimplexCategory.δ i).op) ((X.map (SimplexCategory.σ h).op) t) = x at hi
  have hf : X.map (SimplexCategory.δ i ≫ SimplexCategory.σ h).op t = x := by
    simpa only [op_comp, X.map_comp, types_comp_apply] using hi
  have : Mono (SimplexCategory.δ i ≫ SimplexCategory.σ h) :=
    X.mono_of_nonDegenerate ⟨x, hx⟩ _ t hf
  have he : SimplexCategory.δ i ≫ SimplexCategory.σ h = 𝟙 _ :=
    SimplexCategory.eq_id_of_mono _
  have ht : t = x := by simpa only [he, op_id, X.map_id, types_id_apply] using hf
  have hh₁ : X.δ h.castSucc (X.σ h t) = x := by
    have e : X.δ h.castSucc (X.σ h t) = t :=
      ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := h)) t
    exact e.trans ht
  have hh₂ : X.δ h.succ (X.σ h t) = x := by
    have e : X.δ h.succ (X.σ h t) = t :=
      ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := h)) t
    exact e.trans ht
  have hh : h.castSucc = h.succ := (hu h.castSucc hh₁).trans (hu h.succ hh₂).symm
  have hv := congrArg Fin.val hh
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
