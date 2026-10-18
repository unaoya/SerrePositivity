module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveConstantProduct
public import SerrePositivity.InfinityCategories.F1.WeightedNerveConstantEvaluation

/-!
概要：定値係数の weighted nerve は底の nerve と係数の直積である。
方針：構成済みの直積からの射と最後の係数の評価が互いに逆であることを計算する。
規約：通常の単体集合の実際の同型。係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2、Kerodon §5.3.3。自明作用の hG の写像空間表示。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [SmallCategory C] (X : SSet.{u})

@[reassoc]
lemma constantProduct_evaluation :
    weightedNerveConstantProduct C X ≫ weightedNerveConstantEvaluation C X =
      snd (nerve C) X := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (stdSimplex.map (simplexPrefixInclusion n n _) ≫
    SSet.yonedaEquiv.symm s.2) = s.2
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Equiv.apply_symm_apply]

/-- 概要：定値係数の weighted nerve を直積へ戻す。
方針：底の射影と最後の係数の評価を組にする。
規約：第一因子は底の nerve、第二因子は係数。
使われ方：Goerss–Jardine VIII §2。自明作用の切断のパラメーター表示。 -/
def constantWeightedNerveToProduct :
    weightedNerve ((Functor.const C).obj X) ⟶ nerve C ⊗ X :=
  lift (weightedNerveProjection _) (weightedNerveConstantEvaluation C X)

lemma constantWeightedNerveToProduct_product :
    constantWeightedNerveToProduct C X ≫ weightedNerveConstantProduct C X = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change stdSimplex.map (simplexPrefixInclusion i.val n _) ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (τ.app (Fin.last n))) = τ.app i
  rw [Equiv.symm_apply_apply]
  have h := τ.naturality (homOfLE (Fin.le_last i))
  change stdSimplex.map (simplexPrefixInclusion i.val n _) ≫ τ.app (Fin.last n) =
    τ.app i ≫ 𝟙 X at h
  exact h.trans (Category.comp_id _)

/-- 概要：定値係数の weighted nerve と底との直積の標準同型。
方針：直積からの構成射と、射影・最後の評価による逆射を照合する。
規約：同型は底への射影を保つ。
使われ方：Goerss–Jardine VIII §2、Kerodon §5.3.3。定値図式の homotopy end の比較。 -/
def constantWeightedNerveIso :
    nerve C ⊗ X ≅ weightedNerve ((Functor.const C).obj X) where
  hom := weightedNerveConstantProduct C X
  inv := constantWeightedNerveToProduct C X
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [constantWeightedNerveToProduct, weightedNerveConstantProduct_projection]
    · simp [constantWeightedNerveToProduct, constantProduct_evaluation]
  inv_hom_id := constantWeightedNerveToProduct_product C X

end SerrePositivity.KST.Spectra
