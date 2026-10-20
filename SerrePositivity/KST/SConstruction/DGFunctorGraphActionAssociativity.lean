module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphActions
public import SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorGeneratorMaps

/-! # graph の二段の左作用と三重合成の結合
概要：三重 graph 合成の二経路が持つ、元の Hom 作用の一致を示す。
方針：元の Yoneda balanced 関係に dg Hom 射を前合成し、tensor の自然性で比較する。
規約：元の graph 比較を変更しない。使われ方：三重 graph 合成の結合則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (E : Type v) (T : Type w)
  [DGCategory A E] [DGCategory A T] [Small.{u} T]
variable (U : Type z) [DGCategory A U] [Small.{u} U]

omit [Small.{u} T] in
/-- 合成 graph の左作用は、元の dg Hom 射を後段の graph 左作用へ渡す。 -/
lemma dgFunctorGraph_leftAction_comp (G : DGFunctor A E T) (H : DGFunctor A T U)
    (u : U) (x y : E) :
    BalancedTensor.leftAction A E ((functorGraph A E U (G.comp H)).leftAt u) x y =
      (G.map x y ▷ (u ⟶[Complex A] H.obj (G.obj x))) ≫
        BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) (G.obj x) (G.obj y) := by
  dsimp only [BalancedTensor.leftAction]
  rw [dgFunctorGraph_leftAt_map, dgFunctorGraph_leftAt_map]
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, Category.assoc]
  rw [uncurryRight_precompose]
  rfl

/-- 元の graph 左作用による二経路は、元の tensor 結合同型と両立する。 -/
lemma dgFunctorGraph_leftAction_assoc (G : DGFunctor A E T) (H : DGFunctor A T U)
    (u : U) (t : T) (x y : E) :
    ((x ⟶[Complex A] y) ◁
        BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) t (G.obj x)) ≫
      BalancedTensor.leftAction A E ((functorGraph A E U (G.comp H)).leftAt u) x y =
    (α_ (x ⟶[Complex A] y) (t ⟶[Complex A] G.obj x) (u ⟶[Complex A] H.obj t)).inv ≫
      (BalancedTensor.leftAction A E ((functorGraph A E T G).leftAt t) x y ▷
        (u ⟶[Complex A] H.obj t)) ≫
      BalancedTensor.leftAction A T ((functorGraph A T U H).leftAt u) t (G.obj y) := by
  let N := (functorGraph A T U H).leftAt u
  have hb := tensor_associator_balance
    (BalancedTensor.rightAction A T (representable A (G.obj y)) t (G.obj x))
    (BalancedTensor.leftAction A T N t (G.obj x))
    (BalancedTensor.leftAction A T N t (G.obj y))
    (BalancedTensor.leftAction A T N (G.obj x) (G.obj y))
    ((BalancedTensor.yonedaFamily A T (G.obj y) N).property t (G.obj x))
  rw [dgFunctorGraph_leftAction_comp]
  erw [whisker_exchange_assoc, hb, associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, ← dgFunctorGraph_leftAction_chain]
  rfl

end SerrePositivity.KST.SConstruction
