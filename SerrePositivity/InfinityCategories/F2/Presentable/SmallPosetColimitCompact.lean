module

public import SerrePositivity.InfinityCategories.F2.Presentable.CardinalExchangeReflection
public import SerrePositivity.InfinityCategories.F2.Compact.ColimitClosureExchange

/-!
概要：小さい poset 上の μ-compact 対象の指定余極限頂点は、同じ μ に関して compact。
方針：同じ Hom 全錐族の宇宙へ実証済み交換を移し、元の全余錐の全評価を反映する。
規約：C と指定余極限は u+1、試験添字と κ・μ は u。交換・compact 性を instance で補わない。
使われ方：κ-compact な生成図式の μ-small 部分余極限の μ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Compact
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
  {C : SSet.{u + 1}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C}
  (a : JoinCocone D) (ha : IsColimitCone a)

include h hI ha

/-- 元の小さい poset 図式の全項が μ-compact なら、元の指定余極限頂点も μ-compact。 -/
lemma isMuCompact_smallPosetColimit
    (hD : ∀ k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌,
      IsKappaCompact.{u, u + 1} μ (D.app (Opposite.op ⦋0⦌) k)) :
    IsKappaCompact.{u, u + 1} μ a.vertex := by
  intro B hB hFiltered E c hc
  have : IsKappaFiltered (Cardinal.lift.{u + 1} μ)
      ((SSet.uliftFunctor.{u + 1, u}).obj B) := isKappaFiltered_ulift B
  have hr : IsPointwiseColimitCone (mapJoinCocone
      (coneRestriction ((SSet.uliftFunctor.{u + 2, u + 1}).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).op)
        SpaceInfinity.{u + 1}) (homConeCocone a c)) := by
    rintro ⟨k⟩
    obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k
    exact homConeCocone_right_isColimit a c k (hD k B E c hc)
  have hfull := pointwiseColimit_of_cardinalExchange
    (cardinalFilteredLimitExchangeShape_ulift_poset_op.{u, u + 1} h I hI)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map E ≫ colimitRepresentableFamily a)
    (homConeCocone_inner_isLimit a ha) (homConeCocone a c)
    (homConeCocone_vertex_isLimit a ha c) hr
  exact homConeCocone_apex_isColimit a c hfull

/-- 元の κ-compact な全項の同じ μ-small poset 余極限は、μ-compact になる。 -/
lemma isMuCompact_smallPosetColimit_of_kappaCompact
    (hD : ∀ k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌,
      IsKappaCompact.{u, u + 1} κ (D.app (Opposite.op ⦋0⦌) k)) :
    IsKappaCompact.{u, u + 1} μ a.vertex :=
  isMuCompact_smallPosetColimit h I hI a ha (fun k ↦ (hD k).of_le h.le)

end SerrePositivity.InfinityCategories.F2.Presentable
