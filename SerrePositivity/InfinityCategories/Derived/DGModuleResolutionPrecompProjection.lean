module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompHom
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionComparisonNaturality
/-!
概要：同じ全 Hom 鎖写像の二射影・比較 cochain・単位・入力像を照合する。
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
/-- 元の入力 Hom への射影は、同じ H.map と厳密に可換。 -/
lemma dgModuleResolutionPrecompHom_source
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleResolutionPrecompHom R A C E H F X Y ≫
      dgModuleFunctorResolutionSourceHomMap R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y) =
    dgModuleFunctorResolutionSourceHomMap R A E (H.comp F) X Y ≫ H.map X.source Y.source := by
  simp only [dgModuleResolutionPrecompHom, dgModuleFunctorResolutionSourceHomMap,
    ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.map_fst]
  rfl
/-- 同じ半自由出力 Hom への射影を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_replacement
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleResolutionPrecompHom R A C E H F X Y ≫
      dgModuleFunctorResolutionReplacementHomMap R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y) =
    dgModuleFunctorResolutionReplacementHomMap R A E (H.comp F) X Y := by
  simp only [dgModuleResolutionPrecompHom, dgModuleFunctorResolutionReplacementHomMap,
    ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.map_snd, Category.comp_id]
/-- 同じ実比較 cochain を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_comparison
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleFunctorResolutionHomComparison R C E F
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y) _
      (dgModuleResolutionPrecompHom R A C E H F X Y) =
      dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y := by
  have h := complexMappingCoconeMap_snd
    (dgModuleFunctorResolutionDifference R A E (H.comp F) X Y)
    (dgModuleFunctorResolutionDifference R C E F
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y))
    (biprod.map (H.map X.source Y.source) (𝟙 _)) (𝟙 _)
    (by rw [Category.comp_id]; exact dgModuleResolutionPrecomp_difference R A C E H F X Y)
  simpa only [Cochain.comp_id] using! h
/-- 同じ全 Hom 鎖写像は実単位を保つ。 -/
lemma dgModuleResolutionPrecompHom_identity
    (X : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleFunctorResolutionIdentity R A E (H.comp F) X ≫
      dgModuleResolutionPrecompHom R A C E H F X X =
    dgModuleFunctorResolutionIdentity R C E F (dgModuleResolutionPrecompObject R A C E H F X) := by
  apply dgModuleFunctorResolutionHom_ext R C E F
  · rw [Category.assoc, dgModuleResolutionPrecompHom_source,
      ← Category.assoc, dgModuleFunctorResolutionIdentity_source, H.map_id,
      dgModuleFunctorResolutionIdentity_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionPrecompHom_replacement,
      dgModuleFunctorResolutionIdentity_replacement, dgModuleFunctorResolutionIdentity_replacement]
    rfl
  · rw [dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionPrecompHom_comparison,
      dgModuleFunctorResolutionIdentity_comparison]
    exact dgModuleFunctorResolutionIdentity_comparison R A E (H.comp F) X
/-- 同じ入力像への全 Hom 作用を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_image
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleResolutionPrecompHom R A C E H F X Y ≫
      dgModuleFunctorResolutionImageHomMap R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y) =
    dgModuleFunctorResolutionImageHomMap R A E (H.comp F) X Y := by
  dsimp only [dgModuleFunctorResolutionImageHomMap]
  rw [← Category.assoc, dgModuleResolutionPrecompHom_source, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories
