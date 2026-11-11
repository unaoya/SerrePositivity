module

public import SerrePositivity.KST.Comparison.FreeStandardPrepend

/-!
# 零点追加と全射な標準形への正規化の交換

概要：頂点の先頭追加は、単体写像の像分解による正規化と交換する。
方針：像分解の全射と単射の双方に先頭追加を適用して、分解の一意性で計算する。
規約：Segal 1974 Proposition 1.6 の標準単体の自由な退化の収縮の補助。
使われ方：余分な退化と通常の面・退化の恒等式。
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
概要：零点を追加した頂点写像の引き戻しは、元の引き戻しへの零点追加になる。
方針：標準単体の写像を単体圏の合成に直し、零点追加の合成則を使う。
規約：引き戻す射は任意。
使われ方：正規化の単射部分の作用の計算。
-/
theorem simplexConeZero_simplexMap {k l : SimplexCategory} {n : ℕ}
    (θ : k ⟶ l) (x : l ⟶ ⦋n⦌) :
    (Δ[n] : SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).op
      (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x)) =
        SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (θ ≫ x)) := by
  rw [SSet.stdSimplex.map_objEquiv_symm]
  change SSet.stdSimplex.objEquiv.{u}.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_comp]

/--
概要：単体写像の正規化と標準単体の零点追加は交換する。
方針：元の像分解の全射・単射を拡張し、その分解で正規化を計算する。
規約：元の単体写像が全射である必要はない。
使われ方：標準形への余分な退化の自然性。
-/
theorem freeStandardPrepend_normalize {n d : ℕ} {k : SimplexCategory}
    (x : (Δ[n] : SSet.{u}).obj (op k)) (t : ⦋d⦌ ⟶ k) :
    fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d + 1⦌)
      (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv x)))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend t) =
      freeStandardPrependNormalForm
        (fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌) x t) := by
  have hfac : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (factorThruImage t) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (image.ι t) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend t := by rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_comp, image.fac]
  rw [fatNormalize_eq_of_factorization _ _ _ _ _ _ hfac]
  change (⟨⦋(image t).len + 1⦌, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (factorThruImage t), _,
    (Δ[n] : SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (image.ι t)).op
      (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv x)))⟩ :
      FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d + 1⦌)) =
    ⟨⦋(image t).len + 1⦌, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (factorThruImage t), _,
      SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv
        ((Δ[n] : SSet.{u}).map (image.ι t).op x)))⟩
  rw [simplexConeZero_simplexMap]
  congr 2

end SerrePositivity.KST.Comparison
