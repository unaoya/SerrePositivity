module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphTripleGenerators
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 元の graph 合成比較の結合 coherence
概要：元の graph 合成比較の三重結合則を入力等号の移送つきで示す。
方針：元の三重包含上の二経路を照合し、全 Hom 自然な双加群射の等号へ戻す。
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

/-- 元の graph 三重比較の二経路は、各値の同じ chain map である。 -/
lemma dgFunctorGraphComposition_assoc_value (u : U) (d : D) :
    BimoduleTensor.composeValueMap A U E D
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) u d ≫
      (BimoduleCategory.valueEvaluation A U D u d).map
        (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom =
    (BimoduleTensor.associatorValueIso A U T E D
        (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u d).hom ≫
      BimoduleTensor.composeValueMap A U T D
        (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
        (dgFunctorGraphCompositionIso A D E T F G).hom u d ≫
      (BimoduleCategory.valueEvaluation A U D u d).map
        (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom := by
  apply BimoduleTensor.associatorLeft_hom_ext A U T E D
    (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F) u d
    (T := (functorGraph A D U (F.comp (G.comp H))).value u d)
  intro t e
  exact (dgFunctorGraphTriple_left_generator A D E T U F G H u t e d).trans
    ((dgFunctorGraph_leftAction_assoc A E T U G H u t e (F.obj d)).trans
      (dgFunctorGraphTriple_right_generator A D E T U F G H u t e d).symm)

omit [Small.{u} E] [Small.{u} T] in
/-- 結合等号の graph 移送は、同じ元の各値では恒等 chain map。 -/
lemma dgFunctorGraphInputIso_assoc_value (u : U) (d : D) :
    (BimoduleCategory.valueEvaluation A U D u d).map
        (dgFunctorGraphInputIso A D U (strictDGFunctor_comp_assoc F G H)).hom =
      𝟙 ((functorGraph A D U ((F.comp G).comp H)).value u d) := by
  simp only [dgFunctorGraphInputIso, eqToIso.hom, eqToHom_map]
  rfl

/-- 元の三重 graph 比較は、入力結合等号を保つ全 Hom 自然な射として一致する。 -/
lemma dgFunctorGraphCompositionIso_assoc :
    BimoduleTensor.composeMap A U E D
        (dgFunctorGraphCompositionIso A E T U G H).hom
        (𝟙 (BimoduleCategory.of A E D (functorGraph A D E F))) ≫
      (dgFunctorGraphCompositionIso A D E U F (G.comp H)).hom =
    (BimoduleTensor.associatorIso A U T E D
        (functorGraph A T U H) (functorGraph A E T G) (functorGraph A D E F)).hom ≫
      BimoduleTensor.composeMap A U T D
        (𝟙 (BimoduleCategory.of A U T (functorGraph A T U H)))
        (dgFunctorGraphCompositionIso A D E T F G).hom ≫
      (dgFunctorGraphCompositionIso A D T U (F.comp G) H).hom ≫
      (dgFunctorGraphInputIso A D U (strictDGFunctor_comp_assoc F G H)).hom := by
  apply BimoduleCategory.value_hom_ext A U D
  intro u d
  simp only [CategoryTheory.Functor.map_comp, BimoduleTensor.composeMap_value_eval,
    BimoduleTensor.associatorIso_hom_value_eval]
  rw [dgFunctorGraphInputIso_assoc_value]
  erw [Category.comp_id]
  exact dgFunctorGraphComposition_assoc_value A D E T U F G H u d

end SerrePositivity.KST.SConstruction
