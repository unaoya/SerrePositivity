module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyEvaluationActionFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPairPresentation

/-!
概要：動く点に固定 Kan 射を評価した族と、その指定同型の作用を計算する。
方針：評価を全単体で後合成へ同定し、同じ評価写像の像を使う。
規約：元の全係数と指定同型を保持する。
使われ方：二射評価比較の合成則を同じ固定射の後合成へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数で動く点に固定射を評価すると、同じ射による後合成になる。 -/
lemma pointedRightFamilyEvaluation_const {K L : KanObject.{u}} {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj) (f : K ⟶ L) :
    pointedRightFamilyEvaluation x (SSet.const (ULift.up (functorVertex f))) =
      x ≫ (SSet.uliftFunctor.{u + 1, u}).map f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply ULift.ext
  rfl

/-- 同じ元の二固定射の全評価は、その合成射の全評価に厳密に一致する。 -/
lemma pointedRightFamilyEvaluation_const_comp {K M L : KanObject.{u}}
    {P : SSet.{u + 1}} (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (f : K ⟶ M) (g : M ⟶ L) :
    pointedRightFamilyEvaluation
        (pointedRightFamilyEvaluation x (SSet.const (ULift.up (functorVertex f))))
        (SSet.const (ULift.up (functorVertex g))) =
      pointedRightFamilyEvaluation x (SSet.const (ULift.up (functorVertex (f ≫ g)))) := by
  simp only [pointedRightFamilyEvaluation_const, Functor.map_comp, Category.assoc]

/-- 固定射による評価は、同じ指定点同型を後合成した値を保持する。 -/
lemma pointedRightFamilyEvaluationValueIso_const_heq {K L : KanObject.{u}}
    {P : SSet.{u + 1}} {x x' : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj}
    (a : FunctorIso x x') (f : K ⟶ L) :
    HEq (pointedRightFamilyEvaluationValueIso a (SSet.const (ULift.up (functorVertex f))))
      (a.postcomp ((SSet.uliftFunctor.{u + 1, u}).map f)) := by
  let A := (SSet.uliftFunctor.{u + 1, u}).obj K.obj
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)
  let F := pointedRightFamilyEvaluation (fst A H) (snd A H)
  let y : P ⟶ H := SSet.const (ULift.up (functorVertex f))
  have he := functorIsoOfEq_heq ((functorIsoLiftRight a y).postcomp F)
    (show lift x y ≫ F = pointedRightFamilyEvaluation x y by rfl)
    (show lift x' y ≫ F = pointedRightFamilyEvaluation x' y by rfl)
  have hm : functorPairRight y ≫ (ihom P).map F =
      (ihom P).map ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    unfold functorPairRight
    rw [← curry_natural_right]
    change curry (pointedRightFamilyEvaluation (uncurry (𝟙 ((ihom P).obj A)))
      (fst P ((ihom P).obj A) ≫ y)) = _
    dsimp only [y]
    rw [SSet.comp_const, pointedRightFamilyEvaluation_const, curry_natural_right,
      curry_uncurry, Category.id_comp]
  exact he.trans ((functorIsoLiftRight_postcomp_heq_map a y F).trans
    ((vertexIso_map_heq a hm).trans (functorIso_postcomp_vertexMap_heq a _).symm))

end SerrePositivity.InfinityCategories.F2
