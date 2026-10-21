module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecompAugmentationSquare
/-!
概要：元の前合成 augmentation 正方形を、同じ端点のホモトピー類の等式で表す。
方針：前合成後の同じ円柱射の終点だけを nerve の合成式で揃える。
規約：元の指定比較と円柱射を保つ。使われ方：raw factor への特殊化と K-flat の経路比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 元の前合成関手の実 augmentation を、入力 nerve による像の終点で表す。 -/
def dgModuleResolvedPrecompAugmentationHomotopy :
    SSet.Homotopy
      (dgModuleResolvedInfinity R A E (H.comp F) ≫
        dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)))
      (dgNerve.map H ≫ dgNerve.map F) := by
  let B := dgModuleResolvedAugmentationHomotopy R A E (H.comp F)
  exact { h := B.h
          h₀ := B.h₀
          h₁ := by simpa only [dgNerve.map_comp] using! B.h₁
          rel := B.rel }
/-- 元の指定比較の包含後の射と元の augmentation は、同じ型の正方形の等式を満たす。 -/
lemma dgModuleResolvedInfinity_precompIso_augmentation :
    ((dgModuleResolvedInfinity_precompIso R A C E H F).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)))).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleResolvedAugmentationHomotopy R C E F)
          (dgNerve.map H))) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgModuleResolvedPrecompAugmentationHomotopy R A C E H F)) := by
  have h1 := dgModuleResolvedInfinity_precompIso_augmentation_heq R A C E H F
  have h2 := functorHomotopyHom_heq_of_raw_eq
    (dgModuleResolvedAugmentationHomotopy R A E (H.comp F))
    (dgModuleResolvedPrecompAugmentationHomotopy R A C E H F) rfl
  exact eq_of_heq (h1.trans h2)
end SerrePositivity.InfinityCategories
