module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionPrecompHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionComparisonNaturality
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の入力 Hom への射影は、同じ H.map と厳密に可換。 -/
lemma dgModuleResolutionPrecompHom_source
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R A E (H.comp F) X Y ≫ H.map X.source Y.source := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.map_fst]
  rfl
/-- 同じ半自由出力 Hom への射影を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_replacement
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R A E (H.comp F) X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.map_snd, Category.comp_id]
/-- 同じ実比較 cochain を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_comparison
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R C E F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y) _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R A E (H.comp F) X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y))
    (biprod.map (H.map X.source Y.source) (𝟙 _)) (𝟙 _)
    (by rw [Category.comp_id]; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecomp_difference R A C E H F X Y)
  simpa only [Cochain.comp_id] using! h
/-- 同じ全 Hom 鎖写像は実単位を保つ。 -/
lemma dgModuleResolutionPrecompHom_identity
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R A E (H.comp F) X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X X =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R C E F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHom_ext R C E F
  · rw [Category.assoc, dgModuleResolutionPrecompHom_source,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_source, H.map_id,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionPrecompHom_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_replacement]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionPrecompHom_comparison,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_comparison]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_comparison R A E (H.comp F) X
/-- 同じ入力像への全 Hom 作用を厳密に保つ。 -/
lemma dgModuleResolutionPrecompHom_image
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R A E (H.comp F) X Y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap]
  rw [← Category.assoc, dgModuleResolutionPrecompHom_source, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
