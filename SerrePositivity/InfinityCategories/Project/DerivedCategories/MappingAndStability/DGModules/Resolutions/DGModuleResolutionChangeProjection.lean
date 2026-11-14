module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionChangeHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionComparisonNaturality
/-!
概要：分解変更の実 Hom 鎖写像の二射影・比較 cochain と単位保存を照合する。
方針：同じ mapping cocone の全射影式と比較 cochain の一意性を使う。
規約：同じ全 Hom と元の実単位を保持する。使われ方：実分解変更 dg 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 同じ実入力 Hom への射影を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_source :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.comp_id]
  rfl
/-- 同じ半自由出力 Hom への射影を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_replacement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.comp_id]
  rfl
/-- 比較 cochain は、終点の同じ比較射による後合成そのもの。 -/
lemma dgModuleResolutionChangeHom_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R C E G
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y) _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y).comp
      (Cochain.ofHom (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Y.source) (G.obj Y.source) (a Y.source))) (add_zero (-1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd _ _ _ _ _
omit Y in
/-- 同じ実 Hom 鎖写像は、実分解 dg 圏の同じ実単位を保存する。 -/
lemma dgModuleResolutionChangeHom_identity :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X X =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R C E G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHom_ext R C E G
  · rw [Category.assoc, dgModuleResolutionChangeHom_source,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionChangeHom_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_replacement]
    rfl
  · have hz : (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity R C E F X)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X X) (zero_add (-1)) = 0 :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_comparison R C E F X
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionChangeHom_comparison, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      hz, Cochain.zero_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionIdentity_comparison]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
