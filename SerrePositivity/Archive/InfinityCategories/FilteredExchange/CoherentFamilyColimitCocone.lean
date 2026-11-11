module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUniversalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.PointwiseColimitChoiceTransport

/-!
概要：任意の coherent な図式の族に、余極限関手を頂点とする点ごとの普遍余錐を与える。
方針：全図式の普遍余錐を元の族で制限し、元の全余錐との一意性を使う。
規約：族のパラメータに充填性を課さない。使われ方：元の指定余極限錐への輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {A : SSet.{u + 1}}
  (r : A ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})

/-- 元の coherent な族に対する、余極限関手を頂点とする指定普遍余錐。 -/
def coherentFamilyColimitCocone : JoinCocone (internalHomFlipHomEquiv A
    ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} r) :=
  ⟨(reindexFunctorCocone (coherentColimitUniversalCocone B) r).val, by
    apply (reindexFunctorCocone (coherentColimitUniversalCocone B) r).property.trans
    simpa only [Category.comp_id] using (internalHomFlipHomEquiv_pre r (𝟙 _)).symm⟩

/-- 元の族へ制限した普遍余錐は各パラメータで余極限。 -/
lemma coherentFamilyColimitCocone_pointwise :
    IsPointwiseColimitCone (coherentFamilyColimitCocone B r) := by
  intro a
  apply (isColimitCone_iff_of_coconeMap_eq _
    (evaluateFunctorCocone (reindexFunctorCocone (coherentColimitUniversalCocone B) r) a)
    rfl).mpr
  exact ((coherentColimitUniversalCocone_pointwise B).reindex r) a

/-- 元の族の点ごとの普遍余錐の頂点は、元の族への余極限関手の後合成。 -/
lemma coherentFamilyColimitCocone_vertex :
    (coherentFamilyColimitCocone B r).vertex = functorVertex (r ≫ coherentColimitFunctor B) := by
  change ((pre r).app SpaceInfinity.{u}).app (Opposite.op ⦋0⦌)
    (coherentColimitUniversalCocone B).vertex = _
  rw [coherentColimitUniversalCocone_vertex]
  rfl

/-- 元の族へ制限した点ごとの普遍余錐は関手 ∞ 圏でも余極限。 -/
lemma coherentFamilyColimitCocone_isColimit : IsColimitCone (coherentFamilyColimitCocone B r) :=
  isColimitCone_of_pointwise _ (coherentFamilyColimitCocone_pointwise B r)

/-- 元の任意の指定余極限余錐の頂点は、元の族の余極限関手による像と同型。 -/
def coherentFamilyColimitVertexIso
    (c : JoinCocone (internalHomFlipHomEquiv A ((SSet.uliftFunctor.{u + 1, u}).obj B)
      SpaceInfinity.{u} r)) (hc : IsPointwiseColimitCone c) :
    VertexIso c.vertex (functorVertex (r ≫ coherentColimitFunctor B)) := by
  have e := pointwiseColimitConeVertexIso c (coherentFamilyColimitCocone B r) hc
    (coherentFamilyColimitCocone_pointwise B r)
  rw [coherentFamilyColimitCocone_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.F2
