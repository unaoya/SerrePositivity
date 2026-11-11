module

public import SerrePositivity.KST.Spectra.PointedTracedPathLift

/-!
概要：移送した区間の写像 path トレースの四辺を、元の実区間へ厳密に照合する。
方針：引き戻しの二射影と両端の定数 path の式を計算する。
規約：辺全体の等式。使われ方：交換区間の高次自然性を保つ貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.TracedPathLift

variable {T E B : PointedSimplicialSet.{u}} {q : E ⟶ B} {f g : T ⟶ E}
  {P : VerticalPath (PointedObject.toPoint B) (f ≫ q) (g ≫ q)} (L : TracedPathLift q P)

/-- 写像 path の同じ第一射影を、元の Hom に値を取る自由 path 族として読む。 -/
def tracePath : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace (PointedObject.basedHom T B)).right :=
  L.trace ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (PointedObject.basedHom T B) 1)
    (PointedObject.basedHomMap T q)).right

/-- トレースの始辺全体は、移送した区間の元の π 同型による像。 -/
lemma tracePath_start :
    L.tracePath ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (PointedObject.basedHom T B) 1).right =
      L.path.path ≫ (PointedObject.basedHomMap T q).right := by
  have hp := congrArg Under.Hom.right (pullback.condition
    (f := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (PointedObject.basedHom T B) 1)
    (g := PointedObject.basedHomMap T q))
  simp only [Under.comp_right] at hp
  change (L.trace ≫ _) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc]
  exact congrArg (· ≫ (PointedObject.basedHomMap T q).right) L.retraction

/-- トレースの終辺全体は、最初に指定した同じ downstairs 区間。 -/
lemma tracePath_finish :
    L.tracePath ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (PointedObject.basedHom T B) 0).right = P.path :=
  L.projection

private lemma unit_fst (m : PointedObject.basedHom T E ⟶ PointedObject.basedHom T B) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit m).right ≫
        (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (PointedObject.basedHom T B) 1) m).right =
      m.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath (PointedObject.basedHom T B)).right :=
  congrArg Under.Hom.right (pullback.lift_fst ..)

private lemma pointFamily_post (a : T ⟶ E) :
    pointFamily a ≫ (PointedObject.basedHomMap T q).right = pointFamily (a ≫ q) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  exact familyVertex_post a q

/-- トレースの左辺全体は、元の始点の同じ定数 path。 -/
lemma tracePath_zero :
    stdSimplex.δ (1 : Fin 2) ≫ L.tracePath =
      pointFamily (f ≫ q) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath (PointedObject.basedHom T B)).right := by
  change stdSimplex.δ (1 : Fin 2) ≫ (L.trace ≫ _) = _
  rw [← Category.assoc, L.zero, Category.assoc, unit_fst,
    ← Category.assoc, pointFamily_post]

/-- トレースの右辺全体も、元の終点の同じ定数 path。 -/
lemma tracePath_one :
    stdSimplex.δ (0 : Fin 2) ≫ L.tracePath =
      pointFamily (g ≫ q) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath (PointedObject.basedHom T B)).right := by
  change stdSimplex.δ (0 : Fin 2) ≫ (L.trace ≫ _) = _
  rw [← Category.assoc, L.one, Category.assoc, unit_fst,
    ← Category.assoc, pointFamily_post]

end SerrePositivity.KST.Spectra.PointedMapping.TracedPathLift
