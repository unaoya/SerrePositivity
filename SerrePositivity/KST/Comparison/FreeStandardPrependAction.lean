module

public import SerrePositivity.KST.Comparison.FreeStandardNormalization

/-!
# 零点追加と単体作用の交換

概要：自由な退化の標準形への零点追加は、拡張した単体作用と交換する。
方針：単体作用を前合成後の正規化に直し、像分解との交換を適用する。
規約：Segal 1974 Proposition 1.6 の標準単体の余分な退化の恒等式への補助。
使われ方：通常の面・退化との交換の一括した証明。
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
概要：拡張した単体作用の後の標準形は、元の作用の後の標準形への零点追加である。
方針：二つの単体作用を正規化に直し、全射の前合成と零点追加の交換を使う。
規約：単体作用の射の全射性・単射性は不要。
使われ方：余分な退化の通常の面・退化との交換。
-/
theorem freeStandardPrependNormalForm_action {n d r : ℕ} (θ : ⦋r⦌ ⟶ ⦋d⦌)
    (p : FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)) :
    freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋r + 1⦌)
      ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ).op
        (fatNormalFormRealize _ _ (freeStandardPrependNormalForm p))) =
      freeStandardPrependNormalForm
        (freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋r⦌)
          ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map θ.op (fatNormalFormRealize _ _ p))) := by
  rw [freeDegeneraciesNormalForm_action, freeDegeneraciesNormalForm_action]
  change fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋r + 1⦌)
    (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex)))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend p.epi) =
    freeStandardPrependNormalForm
      (fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋r⦌)
        p.simplex (θ ≫ p.epi))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_comp]
  exact freeStandardPrepend_normalize p.simplex (θ ≫ p.epi)

end SerrePositivity.KST.Comparison
