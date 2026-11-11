module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedRightMorphismTransport

/-!
概要：同じパラメータで動く Kan 点と Kan 射の一点 Hom の合成を厳密に計算する。
方針：元の内部 Hom の評価を使い、高次単体の自然性で一点係数の合成を照合する。
規約：始点も射も固定しない。使われ方：二三角形と指定 path の全族の値比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))

/-- 元の同じパラメータで動く Kan 点を、元の動く Kan 射で評価する全族。 -/
def pointedRightFamilyEvaluation : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj L.obj :=
  lift x y ≫ (HomotopyLimits.uliftTensorIso K.obj (SimplicialCategory.sHom K L)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (uncurry (𝟙 (SimplicialCategory.sHom K L)))

/-- 動く一点係数と動く Kan 射の合成は、元の全族の評価の後の一点係数そのもの。 -/
lemma coherentRightPointCoefficient_family :
    lift (x ≫ (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv) y ≫
      coherentHomComposition pointKanObject K L =
    pointedRightFamilyEvaluation x y ≫
      (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso L.obj).inv := by
  apply (cancel_mono ((SSet.uliftFunctor.{u + 1, u}).map
    (pointFunctorEvaluationIso L.obj).hom)).1
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply ULift.ext
  change (y.app n p).down.app n (𝟙 n) (K.obj.map (𝟙 n) (x.app n p).down) =
    L.obj.map (𝟙 n) ((y.app n p).down.app n (𝟙 n) (x.app n p).down)
  simp only [CategoryTheory.Functor.map_id_apply]

end SerrePositivity.InfinityCategories.F2
