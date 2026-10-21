module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrismData
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompFunctor
/-!
概要：入力 dg 関手の前合成は、実 augmentation の全 cochain と両射影を保つ。
方針：比較 cochain と Hom 鎖写像の厳密な射影式を全次数で評価する。
規約：同じ実分解と augmentation を使用する。使われ方：全 prism の入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet CochainComplex HomComplex
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 入力前合成は同じ実比較 cochain の全次数成分を厳密に保つ。 -/
lemma dgModuleAugmentationHomotopyComponent_precomp
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) (n : ℤ)
    (a : GradedHom R X Y n) :
    dgModuleAugmentationHomotopyComponent R C E F
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y) n
      ((dgModuleResolutionPrecompHom R A C E H F X Y).f n a) =
    dgModuleAugmentationHomotopyComponent R A E (H.comp F) X Y n a := by
  have h := Cochain.congr_v (dgModuleResolutionPrecompHom_comparison R A C E H F X Y)
    n (n - 1) (by omega)
  have he := congrArg (fun m => m a) h
  simpa only [dgModuleFunctorResolutionHomComparison, dgModuleAugmentationHomotopyComponent,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using! he

/-- 入力前合成は augmentation の半自由出力側の全 Hom 作用を保つ。 -/
lemma dgModuleAugmentationSource_hom_precomp
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) (n : ℤ)
    (a : GradedHom R X Y n) :
    ((dgModuleAugmentationSource R C E F).map
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y)).f n
      ((dgModuleResolutionPrecompHom R A C E H F X Y).f n a) =
    ((dgModuleAugmentationSource R A E (H.comp F)).map X Y).f n a := by
  have h := congrArg (fun m => m.f n a)
    (dgModuleResolutionPrecompHom_replacement R A C E H F X Y)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply] using! h
/-- 入力前合成は augmentation の元の入力像側の全 Hom 作用を保つ。 -/
lemma dgModuleAugmentationTarget_hom_precomp
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) (n : ℤ)
    (a : GradedHom R X Y n) :
    ((dgModuleAugmentationTarget R C E F).map
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y)).f n
      ((dgModuleResolutionPrecompHom R A C E H F X Y).f n a) =
    ((dgModuleAugmentationTarget R A E (H.comp F)).map X Y).f n a := by
  have h := congrArg (fun m => m.f n a)
    (dgModuleResolutionPrecompHom_image R A C E H F X Y)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply] using! h
end SerrePositivity.InfinityCategories
