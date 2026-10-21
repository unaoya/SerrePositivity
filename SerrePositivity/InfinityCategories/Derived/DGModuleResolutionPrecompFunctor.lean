module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompPrimitive
/-!
概要：実全 Hom 合成の保存から、前合成に沿う同じ実分解 dg 関手を構成する。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ全 Hom 鎖写像は実合成を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_composition
    (X Y Z : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleFunctorResolutionComposition R A E (H.comp F) X Y Z ≫
      dgModuleResolutionPrecompHom R A C E H F X Z =
    (dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      dgModuleResolutionPrecompHom R A C E H F Y Z) ≫
      dgModuleFunctorResolutionComposition R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y)
        (dgModuleResolutionPrecompObject R A C E H F Z) := by
  apply dgModuleFunctorResolutionHom_ext R C E F
  · rw [Category.assoc, dgModuleResolutionPrecompHom_source,
      ← Category.assoc, dgModuleFunctorResolutionComposition_source, Category.assoc,
      dgModuleFunctorResolutionComposition_source]
    dsimp only [dgModuleFunctorResolutionSourceComposite]
    rw [Category.assoc, H.map_comp, ← Category.assoc, tensorHom_comp_tensorHom,
      ← Category.assoc, tensorHom_comp_tensorHom,
      dgModuleResolutionPrecompHom_source, dgModuleResolutionPrecompHom_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionPrecompHom_replacement,
      dgModuleFunctorResolutionComposition_replacement, Category.assoc,
      dgModuleFunctorResolutionComposition_replacement]
    dsimp only [dgModuleFunctorResolutionReplacementComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      dgModuleResolutionPrecompHom_replacement, dgModuleResolutionPrecompHom_replacement]
    rfl
  · rw [dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionPrecompHom_comparison,
      dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleFunctorResolutionComposition_comparison,
      dgModuleResolutionPrecomp_compositePrimitive]
    exact dgModuleFunctorResolutionComposition_comparison R A E (H.comp F) X Y Z
/-- 入力前合成に沿う、同じ出力と augmentation を保つ実 dg 関手。 -/
def dgModuleResolutionPrecompFunctor :
    DGFunctor R (DGModuleFunctorResolutionObject R A E (H.comp F))
      (DGModuleFunctorResolutionObject R C E F) where
  obj := dgModuleResolutionPrecompObject R A C E H F
  map := dgModuleResolutionPrecompHom R A C E H F
  map_id X := dgModuleResolutionPrecompHom_identity R A C E H F X
  map_comp X Y Z := dgModuleResolutionPrecompHom_composition R A C E H F X Y Z
end SerrePositivity.InfinityCategories
