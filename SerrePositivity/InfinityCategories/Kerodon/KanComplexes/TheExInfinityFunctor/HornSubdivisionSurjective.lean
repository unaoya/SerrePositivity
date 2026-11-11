module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFaceNerveCover
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionInclusion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# horn の細分比較の全射性

概要：実際の horn の細分から、その面の部分順序集合の nerve への比較は全射である。
方針：各 nerve の単体を余面の細分から持ち上げ、細分比較の包含との可換性を使う。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分の像の同定の一方向。
使われ方：細分比較の同型性の全射側。単射性は別項目。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits
open scoped _root_.Simplicial

/--
概要：horn の面の nerve の包含は各次数で単射である。
方針：全ての頂点の像の一致から、部分型の頂点と薄い圏の関手を復元する。
規約：horn の次元について正次元の仮定は不要。
使われ方：細分比較の等式を全ての面の nerve で確認する。
-/
theorem hornFaceInclusion_nerve_app_injective (n : ℕ) (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((nerveMap (hornFaceInclusion.{u} n k).monotone.functor).app d) := by
  intro a b h
  apply nerve.ext_of_isThin
  funext i
  apply Subtype.ext
  exact congrArg (fun s : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d => s.obj i) h

/--
概要：一つの余面の細分からの写像は、horn の細分比較と包含を経て通常の細分された余面になる。
方針：比較の包含との可換性、horn の余面の境界式、標準細分同型の自然性を使う。
規約：最初に標準細分同型の逆で実際の細分へ戻す。
使われ方：面の nerve の単体の具体的な原像。
-/
theorem hornSubdivisionComparison_face (n : ℕ) (k j : Fin (n + 2)) (hj : j ≠ k) :
    SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫ SSet.sd.map (SSet.horn.ι.{u} k j hj) ≫
      hornSubdivisionComparison (n + 1) k ≫
      nerveMap (hornFaceInclusion (n + 1) k).monotone.functor =
        SimplexCategory.sd.map (SimplexCategory.δ j) := by
  calc
    _ = SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫
        SSet.sd.map (SSet.horn.ι k j hj ≫ (SSet.horn (n + 1) k).ι) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌ := by
      rw [SSet.sd.map_comp, Category.assoc, hornSubdivisionComparison_inclusion]
    _ = SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫
        SSet.sd.map (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌ := by rw [SSet.horn.ι_ι]; rfl
    _ = _ := by
      have hn : SSet.sd.map (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌ =
        SSet.stdSimplex.sdIso.hom.app ⦋n⦌ ≫ SimplexCategory.sd.map (SimplexCategory.δ j) :=
        SSet.stdSimplex.sdIso.hom.naturality (SimplexCategory.δ j)
      rw [hn]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/--
概要：正次元 horn の実際の細分比較は各次数で全射である。
方針：面の nerve の単体を一つの余面で覆い、その余面の実際の細分を horn へ送る。
規約：原像は余面の分裂から具体的に与える。
使われ方：細分比較の epi 性。
-/
theorem hornSubdivisionComparison_app_surjective (n : ℕ) (k : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) :
    Function.Surjective ((hornSubdivisionComparison.{u} (n + 1) k).app d) := by
  intro s
  obtain ⟨j, hj, t, ht⟩ := hornFaceNerve_faceCover n k d s
  refine ⟨((SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫ SSet.sd.map (SSet.horn.ι k j hj)).app d) t, ?_⟩
  apply hornFaceInclusion_nerve_app_injective (n + 1) k d
  have h := ConcreteCategory.congr_hom (congr_app (hornSubdivisionComparison_face n k j hj) d) t
  exact h.trans ht

/--
概要：正次元 horn の実際の細分比較は epi である。
方針：各次数での全射性を前層の epi 性へ移す。
規約：単射性や同型性はここでは主張しない。
使われ方：細分した horn の像の同定。
-/
instance hornSubdivisionComparison_epi (n : ℕ) (k : Fin (n + 2)) :
    Epi (hornSubdivisionComparison.{u} (n + 1) k) := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  exact (CategoryTheory.epi_iff_surjective _).mpr (hornSubdivisionComparison_app_surjective n k d)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
