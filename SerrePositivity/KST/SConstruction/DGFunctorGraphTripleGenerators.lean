module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphActionAssociativity
public import SerrePositivity.KST.SConstruction.DGGraphGeneratorPasting
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 元の三重 graph 比較を coend 包含上で計算する
概要：元の三重 graph 比較の二経路を、graph の左作用に帰着する。
方針：tensor の生成元射の合成則と元の graph 比較の Yoneda 評価を使う。
規約：全て元の比較射を用いる。使われ方：graph 合成比較の結合 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z) (U : Type q)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] [DGCategory A U] [Small.{u} U]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (H : DGFunctor A T U)

/-- 内側の二 graph を先に合成する経路の、元の三重包含上の値。 -/
lemma dgFunctorGraphTriple_left_generator (u : U) (t : T) (e : E) (d : D) :
    BimoduleTensor.associatorLeftι A U T E D
        (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u t e d ≫
      BimoduleTensor.composeValueMap A U E D
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) u d ≫
      (BimoduleCategory.valueEvaluation A U D u d).map
        (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom =
    ((e ⟶[Complex A] F.obj d) ◁
      BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) t (G.obj e)) ≫
      BalancedTensor.leftAction A E ((functorGraph A E U (G.comp H)).leftAt u) e (F.obj d) := by
  have ho := BimoduleTensor.ι_composeValueMap A U E D
    (dgFunctorGraphCompositionIso A E T U G H).hom
    (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) u e d
  rw [CategoryTheory.Functor.map_id] at ho
  have ht := dgTensorLeft_generator_comp
    (BalancedTensor.ι A T ((functorGraph A E T G).rightAt e)
      ((functorGraph A T U H).leftAt u) t)
    (BalancedTensor.ι A E ((functorGraph A D E F).rightAt d)
      ((BimoduleTensor.compose A U T E (functorGraph A T U H)
        (functorGraph A E T G)).leftAt u) e)
    (BimoduleTensor.composeValueMap A U E D (dgFunctorGraphCompositionIso A E T U G H).hom
      (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) u d)
    ((BimoduleCategory.valueEvaluation A U E u e).map
      (dgFunctorGraphCompositionIso A E T U G H).hom)
    (BalancedTensor.ι A E ((functorGraph A D E F).rightAt d)
      ((functorGraph A E U (G.comp H)).leftAt u) e)
    (BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) t (G.obj e))
    ((BimoduleCategory.valueEvaluation A U D u d).map
      (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom)
    (BalancedTensor.leftAction A E ((functorGraph A E U (G.comp H)).leftAt u) e (F.obj d))
    ho (dgFunctorGraphComposition_iota A T U E G H u e t)
    (dgFunctorGraphComposition_iota A E U D F (G.comp H) u d e)
  exact ht


/-- 外側の二 graph を先に合成する経路の、元の三重包含上の値。 -/
lemma dgFunctorGraphTriple_right_generator (u : U) (t : T) (e : E) (d : D) :
    BimoduleTensor.associatorLeftι A U T E D
        (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u t e d ≫
      (BimoduleTensor.associatorValueIso A U T E D
        (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u d).hom ≫
      BimoduleTensor.composeValueMap A U T D
        (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
        (dgFunctorGraphCompositionIso A D E T F G).hom u d ≫
      (BimoduleCategory.valueEvaluation A U D u d).map
        (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom =
    (α_ (e ⟶[Complex A] F.obj d) (t ⟶[Complex A] G.obj e)
      (u ⟶[Complex A] H.obj t)).inv ≫
      (BalancedTensor.leftAction A E ((functorGraph A E T G).leftAt t) e (F.obj d) ▷
        (u ⟶[Complex A] H.obj t)) ≫
      BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) t (G.obj (F.obj d)) := by
  have ho := BimoduleTensor.ι_composeValueMap A U T D
    (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
    (dgFunctorGraphCompositionIso A D E T F G).hom u t d
  rw [CategoryTheory.Functor.map_id] at ho
  have hc := congrArg (fun k => k ≫ BimoduleTensor.composeValueMap A U T D
    (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
    (dgFunctorGraphCompositionIso A D E T F G).hom u d)
    (BimoduleTensor.associatorLeftι_hom A U T E D
      (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u t e d)
  have ht := tensorRight_generator_map
    (BalancedTensor.ι A E ((functorGraph A D E F).rightAt d)
      ((functorGraph A E T G).leftAt t) e)
    (BalancedTensor.ι A T ((BimoduleTensor.compose A T E D
      (functorGraph A E T G) (functorGraph A D E F)).rightAt d)
      ((functorGraph A T U H).leftAt u) t)
    (BimoduleTensor.composeValueMap A U T D
      (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
      (dgFunctorGraphCompositionIso A D E T F G).hom u d)
    ((BimoduleCategory.valueEvaluation A T D t d).map
      (dgFunctorGraphCompositionIso A D E T F G).hom)
    (BalancedTensor.ι A T ((functorGraph A D T (F.comp G)).rightAt d)
      ((functorGraph A T U H).leftAt u) t)
    (BalancedTensor.leftAction A E ((functorGraph A E T G).leftAt t) e (F.obj d)) ho
    (dgFunctorGraphComposition_iota A E T D F G t d e)
  have h := (Category.assoc _ _ _).symm.trans (hc.trans ht)
  have hp := congrArg (fun k => k ≫ (BimoduleCategory.valueEvaluation A U D u d).map
    (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom) h
  simp only [Category.assoc] at hp
  rw [dgFunctorGraphComposition_iota] at hp
  exact hp

end SerrePositivity.KST.SConstruction
