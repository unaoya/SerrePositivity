module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionSurjective
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SubdivisionSimplexCover

/-!
# horn の単体と細分の余面による表示

概要：horn への標準単体の写像を、一つの余面を通る写像に因子化する。
方針：頂点写像の像に欠けた頂点を選び、その余面の分裂で因子化する。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分の像の同定への補助。
使われ方：細分の元の余面による表示と表示の比較。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits Opposite
open scoped _root_.Simplicial

/--
概要：正次元 horn への標準単体の写像は、一つの許された余面を経由する。
方針：Yoneda の単体の像に欠けた頂点を選び、余面の分裂による頂点の復元を使う。
規約：因子化の中間は n 次標準単体。元の単体の次元 m は任意。
使われ方：細分の標準単体表示を余面の細分表示へ移す。
-/
theorem hornSimplexFaceFactorization (n : ℕ) (k : Fin (n + 2)) (m : SimplexCategory)
    (f : SSet.stdSimplex.obj m ⟶ (SSet.horn.{u} (n + 1) k : SSet.{u})) :
    ∃ (j : Fin (n + 2)) (hj : j ≠ k) (g : SSet.stdSimplex.obj m ⟶ Δ[n]),
      g ≫ SSet.horn.ι k j hj = f := by
  let s := SSet.yonedaEquiv f
  have hs := (SSet.mem_horn_iff k s.val).mp s.property
  obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem _).mp hs
  have hjk : j ≠ k := fun h => hj (Or.inr (Set.mem_singleton_iff.mpr h))
  let θ := SSet.stdSimplex.objEquiv s.val
  have hθ : θ ≫ simplexFaceRetraction j ≫ SimplexCategory.δ j = θ := by
    apply ConcreteCategory.hom_ext
    intro i
    apply simplexFaceRetraction_recover
    intro h
    exact hj (Or.inl ⟨i, h⟩)
  refine ⟨j, hjk, SSet.stdSimplex.map (θ ≫ simplexFaceRetraction j), ?_⟩
  apply (cancel_mono (SSet.horn (n + 1) k).ι).mp
  rw [Category.assoc, SSet.horn.ι_ι]
  change SSet.stdSimplex.map (θ ≫ simplexFaceRetraction j) ≫
    SSet.stdSimplex.map (SimplexCategory.δ j) = f ≫ (SSet.horn (n + 1) k).ι
  rw [← SSet.stdSimplex.map_comp, Category.assoc, hθ]
  simpa only [s, Equiv.symm_apply_apply] using
    (hornSimplex_yoneda_inclusion (n + 1) k m s).symm

/--
概要：正次元 horn の実際の細分の各単体は、一つの許された余面の細分の像に入る。
方針：密度による標準単体の細分表示を取り、元の horn の単体を余面に因子化する。
規約：細分の比較の全射性とは逆向きの、実際の細分の元の表示。
使われ方：異なる余面表示の一致の証明。
-/
theorem hornSubdivisionFaceCover (n : ℕ) (k : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) (s : (SSet.sd.obj (SSet.horn.{u} (n + 1) k)).obj d) :
    ∃ (j : Fin (n + 2)) (hj : j ≠ k)
      (t : (SSet.sd.obj (Δ[n] : SSet.{u})).obj d),
      (SSet.sd.map (SSet.horn.ι k j hj)).app d t = s := by
  obtain ⟨m, f, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.subdivisionSimplexCover (SSet.horn (n + 1) k) d s
  obtain ⟨j, hj, g, hg⟩ := hornSimplexFaceFactorization n k m f
  refine ⟨j, hj, (SSet.sd.map g).app d t, ?_⟩
  rw [← hg, SSet.sd.map_comp] at ht
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
