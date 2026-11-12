module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeCompositePrimitive
/-!
概要：実分解変更の Hom 鎖写像は、元の二つの実 dg 合成を厳密に保つ。
方針：比較 primitive の二項を合計し、実二射影と比較 cochain の一意性を使う。
規約：全 Hom tensor と元の実合成を保持する。使われ方：分解変更の dg 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
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
variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 合成の同じ比較 cochain 全体は、同じ tensor 鎖写像と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_compositePrimitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive,
    Cochain.comp_add, Cochain.add_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChange_firstPrimitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChange_secondPrimitive]
/-- 同じ実 Hom 鎖写像は、実分解 dg 圏の同じ全 Hom 合成を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_composition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F X Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Z =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHom_ext R C E G
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_source, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_source]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source]
    rfl
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_replacement, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_replacement]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement]
    rfl
  · have hc : (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Z) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_comparison R C E F X Y Z
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_comparison, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      hc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition_comparison,
      dgModuleResolutionChange_compositePrimitive]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
