module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompInfinity
/-!
概要：入力前合成に沿う実分解 dg 関手は、同じ全 Hom と比較 cochain 上で合成を保つ。
方針：二つの射影と比較 cochain の外延性から、指定 dg 関手の厳密等式を得る。
規約：出力分解対象と augmentation を保持する。使われ方：実出力分解の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type v)
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
/-- 二段の入力前合成は、同じ実分解 dg 関手の合成に厳密に一致する。 -/
lemma dgModuleResolutionPrecompFunctor_comp
    (H : DGFunctor R A B) (J : DGFunctor R B C) (F : DGFunctor R C (RightModule R E)) :
    dgModuleResolutionPrecompFunctor R A C E (H.comp J) F =
      (dgModuleResolutionPrecompFunctor R A B E H (J.comp F)).comp
        (dgModuleResolutionPrecompFunctor R B C E J F) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := dgModuleResolutionPrecompFunctor R A C E (H.comp J) F)
    (G := (dgModuleResolutionPrecompFunctor R A B E H (J.comp F)).comp
      (dgModuleResolutionPrecompFunctor R B C E J F)) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    eqToHom_refl, Category.comp_id]
  let X' := dgModuleResolutionPrecompObject R A B E H (J.comp F) X
  let Y' := dgModuleResolutionPrecompObject R A B E H (J.comp F) Y
  let f := dgModuleResolutionPrecompHom R A B E H (J.comp F) X Y
  let g := dgModuleResolutionPrecompHom R B C E J F X' Y'
  apply dgModuleFunctorResolutionHom_ext R C E F
  · have h1 := dgModuleResolutionPrecompHom_source R A C E (H.comp J) F X Y
    have h2 := dgModuleResolutionPrecompHom_source R B C E J F X' Y'
    have h3 := dgModuleResolutionPrecompHom_source R A B E H (J.comp F) X Y
    have h23 := congrArg (fun t => f ≫ t) h2
    simp only [← Category.assoc] at h23
    rw [h3] at h23
    calc
      _ = dgModuleFunctorResolutionSourceHomMap R A E ((H.comp J).comp F) X Y ≫
          H.map X.source Y.source ≫ J.map (H.obj X.source) (H.obj Y.source) := by
        simpa only [EnrichedFunctor.comp_map, Category.assoc] using! h1
      _ = _ := by simpa only [Category.assoc] using! h23.symm
  · have h1 := dgModuleResolutionPrecompHom_replacement R A C E (H.comp J) F X Y
    have h2 := dgModuleResolutionPrecompHom_replacement R B C E J F X' Y'
    have h3 := dgModuleResolutionPrecompHom_replacement R A B E H (J.comp F) X Y
    have h23 := congrArg (fun t => f ≫ t) h2
    rw [h3] at h23
    exact h1.trans (by simpa only [Category.assoc] using! h23.symm)
  · have h1 := dgModuleResolutionPrecompHom_comparison R A C E (H.comp J) F X Y
    have h2 := dgModuleFunctorResolutionHomComparison_precompose R C E F
      (dgModuleResolutionPrecompObject R B C E J F X')
      (dgModuleResolutionPrecompObject R B C E J F Y') f g
    rw [dgModuleResolutionPrecompHom_comparison] at h2
    have h3 := dgModuleResolutionPrecompHom_comparison R A B E H (J.comp F) X Y
    have h23 : dgModuleFunctorResolutionHomComparison R C E F
        (dgModuleResolutionPrecompObject R B C E J F X')
        (dgModuleResolutionPrecompObject R B C E J F Y') _ (f ≫ g) =
        dgModuleFunctorResolutionPrimitive R A E (H.comp (J.comp F)) X Y :=
      h2.trans h3
    exact h1.trans (by simpa only using! h23.symm)
end SerrePositivity.InfinityCategories
