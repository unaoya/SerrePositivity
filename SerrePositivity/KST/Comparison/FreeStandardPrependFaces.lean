module

public import SerrePositivity.KST.Comparison.FreeStandardPrependAction

/-!
# 零点追加の最初の面と自然性

概要：標準単体の自由な退化への零点追加は最初の面で元に戻り、拡張した単体作用と交換する。
方針：全射な標準形の一意性で元を比較し、像分解による計算を使う。
規約：Segal 1974 Proposition 1.6 の余分な退化による収縮の準備。
使われ方：余分な退化の面と退化の恒等式。
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
概要：零点を追加した標準形の最初の面は元の標準形である。
方針：拡張した全射から最初の頂点を除き、元の全射と最初の面で像分解を計算する。
規約：任意の全射な標準形に適用する。
使われ方：余分な退化の最初の面の恒等式。
-/
theorem freeStandardPrependNormalForm_δ_zero {n d : ℕ}
    (p : FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)) :
    freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋d⦌)
      ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map (SimplexCategory.δ 0).op
        (fatNormalFormRealize _ _ (freeStandardPrependNormalForm p))) = p := by
  let : Epi p.epi := p.epi_property
  rw [freeDegeneraciesNormalForm_action]
  change fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)
    (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex)))
    (SimplexCategory.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend p.epi) = p
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ_zero]
  rw [fatNormalize_eq_of_factorization _ _ _ _ p.epi (SimplexCategory.δ 0) rfl]
  have hv : (Δ[n] : SSet.{u}).map (SimplexCategory.δ 0).op
      (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex))) =
      p.simplex := by
    rw [SSet.stdSimplex.map_objEquiv_symm]
    change SSet.stdSimplex.objEquiv.{u}.symm
      (SimplexCategory.δ 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_δ_zero, Equiv.symm_apply_apply]
  change (⟨p.degree, p.epi, _, (Δ[n] : SSet.{u}).map (SimplexCategory.δ 0).op
    (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex)))⟩ :
    FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)) = p
  rw [hv]

/--
概要：零点追加と最初の面の合成は恒等写像。
方針：標準形との同値を使い、最初の面の計算へ帰着する。
規約：単体集合の異なる次数の射の合成として述べる。
使われ方：余分な退化の恒等式。
-/
theorem freeStandardPrepend_δ_zero (n d : ℕ) :
    freeStandardPrepend.{u} n d ≫
      (freeDegeneracies.obj (Δ[n] : SSet.{u})).δ (0 : Fin (d + 2)) = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋d⦌)).injective
  exact freeStandardPrependNormalForm_δ_zero (freeDegeneraciesNormalForm _ _ x)

/--
概要：零点追加は、元の単体作用と拡張した単体作用を交換する。
方針：両辺を標準形で比較して、正規化と先頭追加の交換を適用する。
規約：任意の単体圏の射で成り立つ。
使われ方：余分な退化と通常の面・退化との恒等式。
-/
theorem freeStandardPrepend_naturality {n d r : ℕ} (θ : ⦋r⦌ ⟶ ⦋d⦌) :
    freeStandardPrepend.{u} n d ≫
      (freeDegeneracies.obj (Δ[n] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).op =
    (freeDegeneracies.obj (Δ[n] : SSet.{u})).map θ.op ≫ freeStandardPrepend n r := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋r + 1⦌)).injective
  change freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋r + 1⦌)
      ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).op
        (fatNormalFormRealize _ _
          (freeStandardPrependNormalForm (freeDegeneraciesNormalForm _ _ x)))) =
    fatDegreeNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋r + 1⦌)
      (fatNormalFormRealize _ _ (freeStandardPrependNormalForm
        (freeDegeneraciesNormalForm _ _ ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map θ.op x))))
  rw [fatDegreeNormalize_realize, freeStandardPrependNormalForm_action]
  have hx : fatNormalFormRealize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)
      (freeDegeneraciesNormalForm _ _ x) = x := fatNormalFormRealize_degreeNormalize _ _ x
  rw [hx]

end SerrePositivity.KST.Comparison
