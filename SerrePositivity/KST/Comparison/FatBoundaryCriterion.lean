module

public import SerrePositivity.KST.Comparison.FatSkeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# 有限骨格の逆像と標準単体の境界

概要：新しい行の元が旧骨格に入ることを、標準単体の境界に入ることと同定する。
方針：単体写像の像の次元が下がることと、全射でないことの同値を使う。
規約：Segal 1974 Proposition 1.6 の一段階の付着。
使われ方：境界の積の厳密な引き戻しと pushout の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped _root_.Simplicial

/--
概要：正次元の単体への射の像の次元が小さいことは、その射が全射でないことと同値。
方針：全射の像の計算と、同じ次元の単射は同型であることを使う。
規約：小さい次元の上限は n、終域は n+1 次元。
使われ方：旧骨格への包含と境界の判定。
-/
theorem simplexImage_len_le_iff_not_epi {X : SimplexCategory} (n : ℕ)
    (t : X ⟶ ⦋n + 1⦌) : (image t).len ≤ n ↔ ¬Epi t := by
  constructor
  · intro h he
    let : Epi t := he
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi t] at h
    change n + 1 ≤ n at h
    omega
  · intro h
    have hle := SimplexCategory.len_le_of_mono (image.ι t)
    by_contra hn
    have hlen : (image t).len = n + 1 := by change (image t).len ≤ n + 1 at hle; omega
    let : IsIso (image.ι t) := (SimplexCategory.isIso_iff_of_mono _).mpr hlen
    apply h
    rw [← image.fac t]
    infer_instance

/--
概要：n+1 行の元が n 骨格に入ることは、標準単体の元が境界に入ることと同値。
方針：包含での正規化と、像の次元・非全射性の同値を使う。
規約：境界は Mathlib の標準単体の境界そのもの。
使われ方：新しい行の境界から旧骨格への付着写像。
-/
theorem fatRealizationInclusion_mem_skeleton_iff_boundary
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (x : (F.obj (op ⦋n + 1⦌)).obj d) (t : Δ[n + 1].obj d) :
    (fatRealizationInclusion F (n + 1)).app d (x, t) ∈ (fatSkeleton F n).obj d ↔
      t ∈ (SSet.boundary (n + 1)).obj d := by
  change (fatDegreeNormalize F d
    ((fatRealizationInclusion F (n + 1)).app d (x, t))).degree.len ≤ n ↔ _
  rw [fatDegreeNormalize_inclusion]
  change (image (SSet.stdSimplex.objEquiv t)).len ≤ n ↔
    ¬Function.Surjective (SSet.stdSimplex.objEquiv t).toOrderHom
  simpa only [SimplexCategory.epi_iff_surjective] using
    simplexImage_len_le_iff_not_epi n (SSet.stdSimplex.objEquiv t)

end SerrePositivity.KST.Comparison
