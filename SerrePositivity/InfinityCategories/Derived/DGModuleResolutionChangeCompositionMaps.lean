module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeProjection
public import SerrePositivity.InfinityCategories.Derived.EnrichedCompositionChange
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
variable (X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 元の全入力 Hom の作用は、同じ終点比較射に関して自然。 -/
lemma dgModuleResolutionChange_image_natural :
    dgModuleFunctorResolutionImageHomMap R C E F Y Z ≫
      moduleHomPostcompose R E (F.obj Y.source) (F.obj Z.source) (G.obj Z.source) (a Z.source) =
    dgModuleResolutionChangeHom R C E a hs hq ha Y Z ≫
      dgModuleFunctorResolutionImageHomMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z) ≫
      moduleHomPrecompose R E (F.obj Y.source) (G.obj Y.source) (G.obj Z.source) (a Y.source) := by
  dsimp only [dgModuleFunctorResolutionImageHomMap]
  simp only [Category.assoc]
  rw [← Category.assoc (dgModuleResolutionChangeHom R C E a hs hq ha Y Z),
    dgModuleResolutionChangeHom_source]
  simpa only [Category.assoc, moduleHomPostcompose, moduleHomPrecompose] using!
    congrArg (fun k => dgModuleFunctorResolutionSourceHomMap R C E F Y Z ≫ k)
      (ha Y.source Z.source)
/-- 第一の実合成作用は、同じ比較鎖写像の tensor と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_firstCompositionMap :
    (moduleHomPostcompose R E X.replacement.val (F.obj Y.source) (G.obj Y.source) (a Y.source) ⊗ₘ
      dgModuleResolutionChangeHom R C E a hs hq ha Y Z) ≫
      dgModuleFunctorResolutionFirstCompositionMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z) =
    dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z ≫
      moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source) := by
  have h := enrichedComposition_natural_parameter (Complex R) (ModuleCategory R E)
    (𝟙 (moduleHom R E X.replacement.val (F.obj Y.source)))
    (dgModuleFunctorResolutionImageHomMap R C E F Y Z)
    (dgModuleResolutionChangeHom R C E a hs hq ha Y Z ≫
      dgModuleFunctorResolutionImageHomMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z))
    (a Y.source) (a Z.source) (dgModuleResolutionChange_image_natural R C E a hs hq ha Y Z)
  simpa only [dgModuleFunctorResolutionFirstCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    moduleHomPostcompose] using! h
/-- 第二の実合成作用も、同じ比較鎖写像の tensor と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_secondCompositionMap :
    (dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      moduleHomPostcompose R E Y.replacement.val (F.obj Z.source) (G.obj Z.source) (a Z.source)) ≫
      dgModuleFunctorResolutionSecondCompositionMap R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z) =
    dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z ≫
      moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source) := by
  have h := enrichedComposition_target_parameter (Complex R) (ModuleCategory R E)
    (dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
    (𝟙 (moduleHom R E Y.replacement.val (F.obj Z.source))) (a Z.source)
  simpa only [dgModuleFunctorResolutionSecondCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, dgModuleResolutionChangeHom_replacement,
    Category.comp_id, Category.id_comp, moduleHomPostcompose] using! h.symm
end SerrePositivity.InfinityCategories
