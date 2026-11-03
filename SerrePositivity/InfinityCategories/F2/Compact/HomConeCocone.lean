module

public import SerrePositivity.InfinityCategories.F2.Compact.HomConeFamily
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：元の指定余錐を、同じ余極限からの全 Hom 錐族で写した全余錐として保持する。
方針：全余錐を後合成し、各生成点と頂点の評価を元の Hom 余錐へ厳密に戻す。
規約：元の両余錐・全高次・各点の同じ像を保持。使われ方：compact 閉性への交換入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {K J C : SSet.{u}} [Quasicategory C] {D : K ⟶ C} {E : J ⟶ C}

/-- 元の指定余錐を、同じ全 Hom 錐族への全余錐として写す。 -/
def homConeCocone (a : JoinCocone D) (c : JoinCocone E) :=
  mapJoinCocone (colimitRepresentableFamily a) (JoinCocone.ulift.{u, u + 1} c)

/-- 元の族の各点は、元の余極限からの全 Hom の極限錐。 -/
lemma homConeCocone_inner_isLimit (a : JoinCocone D) (ha : IsColimitCone a)
    (j : J _⦋0⦌) :
    IsLimitCone (functorVertexCone
      (((SSet.uliftFunctor.{u + 1, u}).map E ≫ colimitRepresentableFamily a).app
        (Opposite.op ⦋0⦌) (ULift.up j))) :=
  colimitRepresentableFamily_isLimit a ha (E.app (Opposite.op ⦋0⦌) j)

/-- 元の指定余錐像の頂点も、元の余極限からの全 Hom の極限錐。 -/
lemma homConeCocone_vertex_isLimit (a : JoinCocone D) (ha : IsColimitCone a)
    (c : JoinCocone E) : IsLimitCone (functorVertexCone (homConeCocone a c).vertex) := by
  rw [homConeCocone, Ind.mapJoinCocone_vertex, JoinCocone.ulift_vertex]
  exact colimitRepresentableFamily_isLimit a ha c.vertex

/-- 元の生成点での全余錐評価は、元のその項からの Hom による同じ余錐像。 -/
lemma homConeCocone_right_isColimit (a : JoinCocone D) (c : JoinCocone E) (k : K _⦋0⦌)
    (h : IsColimitCone (mapJoinCocone (covariantRepresentableInfinity
      (D.app (Opposite.op ⦋0⦌) k)) (JoinCocone.ulift.{u, u + 1} c))) :
    IsColimitCone (evaluateFunctorCocone (mapJoinCocone
      (coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K.op) SpaceInfinity.{u})
      (homConeCocone a c)) (ULift.up (SSet.opObjEquiv.symm k))) := by
  apply (isColimitCone_iff_of_coconeMap_eq _
    (mapJoinCocone (covariantRepresentableInfinity (D.app (Opposite.op ⦋0⦌) k))
      (JoinCocone.ulift c)) ?_).mpr h
  change (((JoinCocone.ulift c).val ≫ colimitRepresentableFamily a) ≫ _) ≫ _ = _
  simp only [Category.assoc, coneRestriction, functorCoconePrecomp_evaluate]
  rw [colimitRepresentableFamily_right]
  rfl

/-- 元の頂点での全余錐評価も、元の余極限頂点からの Hom による同じ余錐像。 -/
lemma homConeCocone_apex_isColimit (a : JoinCocone D) (c : JoinCocone E)
    (h : IsPointwiseColimitCone (homConeCocone a c)) :
    IsColimitCone (mapJoinCocone (covariantRepresentableInfinity a.vertex)
      (JoinCocone.ulift.{u, u + 1} c)) := by
  have ht := h (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1})
    ((SSet.uliftFunctor.{u + 1, u}).obj K.op)))
  apply (isColimitCone_iff_of_coconeMap_eq _ _ ?_).mp ht
  change ((JoinCocone.ulift c).val ≫ colimitRepresentableFamily a) ≫ _ = _
  rw [Category.assoc, colimitRepresentableFamily_apex]
  rfl

end SerrePositivity.InfinityCategories.F2.Compact
