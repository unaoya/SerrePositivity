module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConstantIntervalFiberTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedValueRightInverse
public import SerrePositivity.InfinityCategories.F1.CoherentKanRightCompositionTransport
public import SerrePositivity.InfinityCategories.F1.CoherentHomIntervalVertices
public import SerrePositivity.InfinityCategories.F1.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedTensorCoefficient

/-!
概要：元の Kan 射を右 Hom の区間族で表示し、一点 Hom の係数作用を計算する。
方針：元の coherent 辺の端点表示だけを揃え、動く一点係数の後合成を計算する。
規約：高次の一点係数を保持。使われ方：既存の値比較の輸送自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 既存の一点 Hom の標準同型は、唯一の頂点での評価による同型と一致する。 -/
lemma pointKanHomIso_eq_evaluation (K : KanObject.{u}) :
    pointKanObjectHomIso K = pointFunctorEvaluationIso K.obj := by
  apply Iso.ext
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 元の Kan 射の辺を、既存の空間の標準頂点の端点表示で保持する。 -/
def pointedRightMorphismEdge {K L : KanObject.{u}} (f : K ⟶ L) :
    SSet.Edge (spaceInfinityVertex K) (spaceInfinityVertex L) :=
  (coherentNerveEdge f).ofEq (spaceInfinityVertex_eq_coherent K).symm
    (spaceInfinityVertex_eq_coherent L).symm

/-- 元の Kan 射の右 Hom 区間頂点は、同じ coherent 辺の端点表示を移した頂点。 -/
lemma coherentKanRightHomInterval_morphism {K L : KanObject.{u}} (f : K ⟶ L) :
    (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up (functorVertex f)) = intervalMappingVertexOfEdge (pointedRightMorphismEdge f) := by
  change (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex K) (coherentNerveVertex L)
    (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm).app _
      ((coherentHomIntervalComparison K L).app _ (ULift.up (functorVertex f))) = _
  rw [coherentHomIntervalComparison_vertex, intervalMappingPostOfEq_vertex]
  rfl

/-- 動く一点係数と元の固定 Kan 射の合成は、元の Kan 射の後に一点評価の逆を続ける。 -/
lemma coherentRightPointCoefficient_post {K L : KanObject.{u}} (f : K ⟶ L) :
    lift ((SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv)
      (SSet.const (ULift.up (functorVertex f))) ≫ coherentHomComposition pointKanObject K L =
        (SSet.uliftFunctor.{u + 1, u}).map f ≫
          (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso L.obj).inv := by
  let A := SimplicialCategory.sHom pointKanObject K
  let H := SimplicialCategory.sHom K L
  have hc : (SSet.const (ULift.up (functorVertex f)) :
      (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj H) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (isTerminalTensorUnit.from A ≫ curry' (show K.obj ⟶ L.obj from f)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app ((SSet.unitHomEquiv H).left_inv (curry' f)) n) PUnit.unit
    exact h
  have hp : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A))
      (SSet.const (ULift.up (functorVertex f))) ≫ coherentHomComposition pointKanObject K L =
        (SSet.uliftFunctor.{u + 1, u}).map ((ihom pointKanObject.obj).map f) := by
    rw [hc, ← kanCoefficientPostcomposition pointKanObject f]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hn := pointKanObjectHomNatIso.inv.naturality f
  rw [kanObject_sHomWhiskerLeft] at hn
  change (show K.obj ⟶ L.obj from f) ≫ (pointKanObjectHomIso L).inv =
    (pointKanObjectHomIso K).inv ≫ (ihom pointKanObject.obj).map f at hn
  rw [pointKanHomIso_eq_evaluation, pointKanHomIso_eq_evaluation] at hn
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv ≫
        (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A))
          (SSet.const (ULift.up (functorVertex f))) ≫
            coherentHomComposition pointKanObject K L) := by
      rfl
    _ = _ := by
      rw [hp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (SSet.uliftFunctor.{u + 1, u}).map hn.symm

end SerrePositivity.InfinityCategories.HomotopyLimits
