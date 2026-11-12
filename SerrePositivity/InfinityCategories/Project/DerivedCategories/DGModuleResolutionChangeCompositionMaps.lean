module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedCompositionChange
/-!
概要：実分解変更の Hom 鎖写像は、二つの全合成作用を同じ終点後合成へ送る。
方針：入力射影の厳密等式、全 Hom 自然性、豊穣合成の全パラメータ自然性を使う。
規約：実比較 cochain の二項を別々に保持する。使われ方：分解変更の合成保存。
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
/-- 元の全入力 Hom の作用は、同じ終点比較射に関して自然。 -/
lemma dgModuleResolutionChange_image_natural :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F Y Z ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E (F.obj Y.source) (F.obj Z.source) (G.obj Z.source) (a Z.source) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z) ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose R E (F.obj Y.source) (G.obj Y.source) (G.obj Z.source) (a Y.source) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_source]
  simpa only [Category.assoc, _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose, _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose] using!
    congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F Y Z ≫ k)
      (ha Y.source Z.source)
/-- 第一の実合成作用は、同じ比較鎖写像の tensor と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_firstCompositionMap :
    (_root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val (F.obj Y.source) (G.obj Y.source) (a Y.source) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_natural_parameter (Complex R) (ModuleCategory R E)
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val (F.obj Y.source)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z))
    (a Y.source) (a Z.source) (dgModuleResolutionChange_image_natural R C E a hs hq ha Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose] using! h
/-- 第二の実合成作用も、同じ比較鎖写像の tensor と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_secondCompositionMap :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E Y.replacement.val (F.obj Z.source) (G.obj Z.source) (a Z.source)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E G
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeObject R C E a hs hq Z) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_target_parameter (Complex R) (ModuleCategory R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E Y.replacement.val (F.obj Z.source))) (a Z.source)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeHom_replacement,
    Category.comp_id, Category.id_comp, _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose] using! h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
