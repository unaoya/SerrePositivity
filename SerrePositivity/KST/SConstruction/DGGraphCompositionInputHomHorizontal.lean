module
public import SerrePositivity.KST.SConstruction.DGGraphCompositionInputHorizontal
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition

/-! # 元の入力 Hom end の横合成と実 graph tensor の一致
概要：元の入力 Hom end の横合成を、実 graph tensor の全次数作用と同じ比較で照合する。
方針：二つの普遍パラメータを使い、元の横合成の全対象評価を回収する。
規約：入力 Hom end を別の模型へ置換しない。使われ方：厳密豊穣 Perf の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]
  (F F' : DGFunctor A D E) (G G' : DGFunctor A E T)

omit [Small.{u} T] in
/-- 元の二つの普遍 Hom パラメータの横合成は、元の横合成 chain map を表示する。 -/
lemma dgFunctorHorizontal_parameter :
    dgFunctorParamCompose A D T
        (dgFunctorParamPost A D E T G
          (dgFunctorHomEquiv A D E (dgFunctorHom A D E F F') F F' (𝟙 _)))
        (dgFunctorParamPre A E T D F'
          (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _))) =
      dgFunctorHomEquiv A D T (dgFunctorHom A D E F F' ⊗ dgFunctorHom A E T G G')
        (F.comp G) (F'.comp G') (dgFunctorHorizontal A D E T F F' G G') := by
  apply GradedNatTrans.ext
  funext d
  change (((𝟙 _ ≫ dgFunctorHomπ A D E F F' d) ≫ G.map (F.obj d) (F'.obj d)) ⊗ₘ
      (𝟙 _ ≫ dgFunctorHomπ A E T G G' (F'.obj d))) ≫ eComp (Complex A) _ _ _ =
    dgFunctorHorizontal A D E T F F' G G' ≫
      dgFunctorHomπ A D T (F.comp G) (F'.comp G') d
  simp only [Category.id_comp]
  exact (dgFunctorHorizontal_π A D E T F F' G G' d).symm

/-- 元の Hom end の横合成は、同じ graph tensor の作用と比較共役によって回収される。 -/
lemma dgFunctorGraphComposition_inputHom_horizontal (d : D) :
    ((BimoduleTensor.secondParam A T E D (functorGraph A E T G)
          (dgFunctorGraphParameter A D E
            (dgFunctorHomEquiv A D E (dgFunctorHom A D E F F') F F' (𝟙 _)))).app d ⊗ₘ
        (BimoduleTensor.firstParam A T E D (functorGraph A D E F')
          (dgFunctorGraphParameter A E T
            (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _)))).app d) ≫
        moduleComposition A T _ _ _ ≫
          enrichedClosedIsoConjugation (Complex A) (dgFunctorGraphCompositionAt A D E T F G d)
            (dgFunctorGraphCompositionAt A D E T F' G' d) =
      dgFunctorHorizontal A D E T F F' G G' ≫
        dgFunctorHomπ A D T (F.comp G) (F'.comp G') d ≫
          yonedaHom A T (G.obj (F.obj d)) (G'.obj (F'.obj d)) := by
  have h := dgFunctorGraphComposition_parameter_horizontal A D E T
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F F') F F' (𝟙 _))
    (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _)) d
  rw [dgFunctorHorizontal_parameter] at h
  simp only [dgFunctorGraphParameter_app, dgFunctorHomEquiv, Category.assoc] at h ⊢
  convert h using 1
  rfl

end SerrePositivity.KST.SConstruction
