module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompData
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeMap
/-!
概要：前合成に沿う実 mapping cocone の全 Hom 鎖写像を構成する。
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
/-- 入力に H.map、半自由出力と比較 cochain に恒等を使う全鎖写像。 -/
def dgModuleResolutionPrecompHom
    (X Y : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    dgModuleFunctorResolutionHomComplex R A E (H.comp F) X Y ⟶
      dgModuleFunctorResolutionHomComplex R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y) :=
  complexMappingCoconeMap (dgModuleFunctorResolutionDifference R A E (H.comp F) X Y)
    (dgModuleFunctorResolutionDifference R C E F
      (dgModuleResolutionPrecompObject R A C E H F X)
      (dgModuleResolutionPrecompObject R A C E H F Y))
    (biprod.map (H.map X.source Y.source) (𝟙 _)) (𝟙 _)
    (by rw [Category.comp_id]; exact dgModuleResolutionPrecomp_difference R A C E H F X Y)
end SerrePositivity.InfinityCategories
