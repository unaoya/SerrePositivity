module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFaceLifting

/-!
# 二つの細分された余面の共通の表示

概要：二つの異なる余面から同じ細分の単体を表すとき、共通の小さい標準単体から表示できる。
方針：一方の余面の像で欠ける頂点を、他方の余面の中へ戻して、さらに一つの余面で持ち上げる。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分比較の単射性への補助。
使われ方：horn の細分における異なる余面表示の一致。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder
open scoped _root_.Simplicial

/--
概要：異なる余面で表す同じ細分の単体は、両方へ向かう共通の小さい面から来る。
方針：共通の欠けた頂点での持ち上げと、他方の余面の分裂による因子化を使う。
規約：二つの余面の定義域の次元は n+1 で正次元。
使われ方：horn の実際の細分比較の単射性。
-/
theorem subdivisionCommonFace (n : ℕ) (j l : Fin (n + 3)) (hjl : j ≠ l)
    (d : SimplexCategoryᵒᵖ) (t u : (SimplexCategory.sd.{u}.obj ⦋n + 1⦌).obj d)
    (h : (SimplexCategory.sd.map (SimplexCategory.δ j)).app d t =
      (SimplexCategory.sd.map (SimplexCategory.δ l)).app d u) :
    ∃ (α β : ⦋n⦌ ⟶ ⦋n + 1⦌) (v : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d),
      α ≫ SimplexCategory.δ j = β ≫ SimplexCategory.δ l ∧
      (SimplexCategory.sd.map α).app d v = t ∧ (SimplexCategory.sd.map β).app d v = u := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hjl.symm
  have haδ : SimplexCategory.δ j a = l := ha
  have hm : ∀ i, ULift.up a ∉ (t.obj i).finset := by
    intro i hi
    have hl : ULift.up l ∈
        (((SimplexCategory.sd.map (SimplexCategory.δ j)).app d t).obj i).finset := by
      exact (NonemptyFiniteChains.mem_map_iff (t.obj i)
        (SimplexCategory.toPartOrd.map (SimplexCategory.δ j)).hom (ULift.up l)).mpr
          ⟨ULift.up a, hi, congrArg ULift.up haδ⟩
    rw [h] at hl
    exact subdivisionFace_avoids l d u i hl
  obtain ⟨v, hv⟩ := subdivisionFace_lift a d t hm
  let α := SimplexCategory.δ a
  let β := (α ≫ SimplexCategory.δ j) ≫ simplexFaceRetraction l
  have hβ : β ≫ SimplexCategory.δ l = α ≫ SimplexCategory.δ j := by
    apply simplexHom_factor_face
    intro i hi
    have hx : SimplexCategory.δ j (SimplexCategory.δ a i) = SimplexCategory.δ j a :=
      hi.trans haδ.symm
    exact Fin.succAbove_ne a i (Fin.succAbove_right_injective hx)
  refine ⟨α, β, v, hβ.symm, hv, ?_⟩
  apply subdivisionFace_app_injective l d
  have hmap : SimplexCategory.sd.map β ≫ SimplexCategory.sd.map (SimplexCategory.δ l) =
      SimplexCategory.sd.map α ≫ SimplexCategory.sd.map (SimplexCategory.δ j) := by
    rw [← SimplexCategory.sd.map_comp, hβ, SimplexCategory.sd.map_comp]
  calc
    _ = (SimplexCategory.sd.map (SimplexCategory.δ j)).app d
        ((SimplexCategory.sd.map α).app d v) :=
      ConcreteCategory.congr_hom (congr_app hmap d) v
    _ = (SimplexCategory.sd.map (SimplexCategory.δ j)).app d t := congrArg _ hv
    _ = _ := h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
