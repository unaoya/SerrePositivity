module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleFirstTransport
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomNaturality
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNaturalityFactorCoherence

/-!
概要：第二面の分解比較の最初の因子は、元の二回目の底変換自然性を回収する。
方針：同じ最初の面の作用と指定切断の因子比較の前合成則を使う。
規約：元の全 Hom の底変換作用と元の大域自然性を保持する。
使われ方：第二面の指定同型を局所自然性との共有頂点の三角形へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 上で、分解の最初の因子は二回目の底変換自然性そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomFirstTransportIso_naturality_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq ((cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      ((cocartesianBaseChangeHomNaturalityIso l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q))) := by
  let p' := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p
  let q' := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q
  let a := (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q)
  let P₁ := cocartesianBaseChangeHomSpanOne l p' q'
  let P₀ := cocartesianBaseChangeHomSpanZero l p' q'
  let s := cocartesianBaseChangeHomSpanOneSection l p' q'
  have hp : IsFullyFaithful P₁ := cocartesianBaseChangeHomSpanOne_isFullyFaithful l p' q'
  have hs : s ≫ P₁ = 𝟙 _ := cocartesianBaseChangeHomSpanOneSection_projection l p' q'
  let b := cocartesianBaseChangeHomComparison l p' q'
  have h₁ := homSpanSectionTransportFactorIso_precomp_heq P₁ P₀ s hp hs
    (cocartesianBaseChangeSecondTriangleHomFirst l k p q)
    (cocartesianBaseChangeSecondTriangleHomComparison l k p q) (a ≫ b)
    (cocartesianBaseChangeSecondTriangleHomComparison_first l k p q)
  have h₂ := homSpanSectionTransportFactorIso_precomp_heq P₁ P₀ s hp hs b a (a ≫ b) rfl
  have h₃ := F2.functorIso_precomp_heq_of_heq
    (cocartesianBaseChangeHomNaturalityIso l p' q')
    (homSpanSectionTransportFactorIso P₁ P₀ s hp hs b)
    (by
      rw [cocartesianBaseChangeHomComparison_one]
      simp only [cocartesianBaseChangeHomTransport, s, P₀, Category.assoc])
    (cocartesianBaseChangeHomComparison_zero l p' q').symm
    (cocartesianBaseChangeHomNaturalityIso_factor_heq l p' q').symm a
  exact h₁.trans (h₂.symm.trans h₃)

end SerrePositivity.InfinityCategories
