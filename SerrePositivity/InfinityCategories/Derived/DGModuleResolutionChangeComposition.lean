module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeCompositePrimitive
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
/-- 合成の同じ比較 cochain 全体は、同じ tensor 鎖写像と終点後合成に整合する。 -/
lemma dgModuleResolutionChange_compositePrimitive :
    (Cochain.ofHom (dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      dgModuleResolutionChangeHom R C E a hs hq ha Y Z)).comp
      (dgModuleFunctorResolutionCompositePrimitive R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z)) (zero_add (-1)) =
    (dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z).comp
      (Cochain.ofHom (moduleHomPostcompose R E X.replacement.val
        (F.obj Z.source) (G.obj Z.source) (a Z.source))) (add_zero (-1)) := by
  rw [dgModuleFunctorResolutionCompositePrimitive, dgModuleFunctorResolutionCompositePrimitive,
    Cochain.comp_add, Cochain.add_comp,
    dgModuleResolutionChange_firstPrimitive, dgModuleResolutionChange_secondPrimitive]
/-- 同じ実 Hom 鎖写像は、実分解 dg 圏の同じ全 Hom 合成を厳密に保存する。 -/
lemma dgModuleResolutionChangeHom_composition :
    dgModuleFunctorResolutionComposition R C E F X Y Z ≫
      dgModuleResolutionChangeHom R C E a hs hq ha X Z =
    (dgModuleResolutionChangeHom R C E a hs hq ha X Y ⊗ₘ
      dgModuleResolutionChangeHom R C E a hs hq ha Y Z) ≫
      dgModuleFunctorResolutionComposition R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y)
        (dgModuleResolutionChangeObject R C E a hs hq Z) := by
  apply dgModuleFunctorResolutionHom_ext R C E G
  · rw [Category.assoc, dgModuleResolutionChangeHom_source,
      dgModuleFunctorResolutionComposition_source, Category.assoc,
      dgModuleFunctorResolutionComposition_source]
    dsimp only [dgModuleFunctorResolutionSourceComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      dgModuleResolutionChangeHom_source, dgModuleResolutionChangeHom_source]
    rfl
  · rw [Category.assoc, dgModuleResolutionChangeHom_replacement,
      dgModuleFunctorResolutionComposition_replacement, Category.assoc,
      dgModuleFunctorResolutionComposition_replacement]
    dsimp only [dgModuleFunctorResolutionReplacementComposite]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      dgModuleResolutionChangeHom_replacement, dgModuleResolutionChangeHom_replacement]
    rfl
  · have hc : (Cochain.ofHom (dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
        (dgModuleFunctorResolutionPrimitive R C E F X Z) (zero_add (-1)) =
      dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z :=
      dgModuleFunctorResolutionComposition_comparison R C E F X Y Z
    rw [dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleResolutionChangeHom_comparison, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      hc, dgModuleFunctorResolutionHomComparison_precompose,
      dgModuleFunctorResolutionComposition_comparison,
      dgModuleResolutionChange_compositePrimitive]
end SerrePositivity.InfinityCategories
