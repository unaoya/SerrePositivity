module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameterComposition
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHom
public import SerrePositivity.KST.SConstruction.DGParameterUniversal
public import SerrePositivity.KST.SConstruction.DGExtensionParameterPullback

/-! # 元の実加群入力 Hom と前後合成
概要：元の Hom end の前後合成を、同じ実合成比較による入力作用の共役で回収する。
方針：任意 K 作用の普遍入力 Hom 表示と、合成比較の全入力自然性を使う。
規約：元の入力 Hom を保持する。使われ方：実加群の入力横合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 任意 K の元の実加群作用は、同じ普遍入力 Hom 作用への前合成である。 -/
lemma dgModuleExtensionInputHom_factorization {K : Complex A} {F F' : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F F') (M : RightModule A D) :
    (dgFunctorHomEquiv A D E K F F').symm τ ≫ dgModuleExtensionInputHom A D E F F' M =
      (dgModuleExtensionParameter A D E τ).app M := by
  have h := congrArg (fun σ => (dgModuleExtensionParameter A D E σ).app M)
    (dgParameterUniversal_pullback A D E F F' τ)
  rw [dgModuleExtensionParameter_pullback] at h
  exact h

variable (T : Type z) [DGCategory A T] [Small.{u} T]

/-- 元の入力 Hom の後合成は、同じ実加群合成比較の共役で回収される。 -/
lemma dgModuleExtensionInputHom_post {F F' : DGFunctor A D E} (G : DGFunctor A E T)
    (M : RightModule A D) :
    (dgModuleExtensionInputHom A D E F F' M ≫ (dgModuleExtension A E T G).map
        ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F').obj M)) ≫
        enrichedClosedIsoConjugation (Complex A) (dgModuleExtensionCompositionAt A D E T F G M)
          (dgModuleExtensionCompositionAt A D E T F' G M) =
      dgFunctorHomPost A D E T G F F' ≫
        dgModuleExtensionInputHom A D T (F.comp G) (F'.comp G) M := by
  have h := dgModuleExtensionComposition_parameter_post A D E T G
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F F') F F' (𝟙 _)) M
  exact h.trans (dgModuleExtensionInputHom_factorization A D T
    (dgFunctorParamPost A D E T G
      (dgFunctorHomEquiv A D E (dgFunctorHom A D E F F') F F' (𝟙 _))) M).symm

/-- 元の入力 Hom の前合成は、同じ実加群合成比較の共役で回収される。 -/
lemma dgModuleExtensionInputHom_pre {G G' : DGFunctor A E T} (F : DGFunctor A D E)
    (M : RightModule A D) :
    dgModuleExtensionInputHom A E T G G' ((dgModuleExtension A D E F).obj M) ≫
        enrichedClosedIsoConjugation (Complex A) (dgModuleExtensionCompositionAt A D E T F G M)
          (dgModuleExtensionCompositionAt A D E T F G' M) =
      dgFunctorHomPre A E T D F G G' ≫
        dgModuleExtensionInputHom A D T (F.comp G) (F.comp G') M := by
  have h := dgModuleExtensionComposition_parameter_pre A D E T F
    (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _)) M
  exact h.trans (dgModuleExtensionInputHom_factorization A D T
    (dgFunctorParamPre A E T D F
      (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _))) M).symm

end SerrePositivity.KST.SConstruction
