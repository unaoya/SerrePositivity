module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalExchangeReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ColimitClosureExchange

/-!
概要：小さい poset 上の μ-compact 対象の指定余極限頂点は、同じ μ に関して compact。
方針：同じ Hom 全錐族の宇宙へ実証済み交換を移し、元の全余錐の全評価を反映する。
規約：C と指定余極限は u+1、試験添字と κ・μ は u。交換・compact 性を instance で補わない。
使われ方：κ-compact な生成図式の μ-small 部分余極限の μ-compact 性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
  {C : SSet.{u + 1}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C}
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a)

include h hI ha

/-- 元の小さい poset 図式の全項が μ-compact なら、元の指定余極限頂点も μ-compact。 -/
lemma isMuCompact_smallPosetColimit
    (hD : ∀ k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ a.vertex := by
  intro B hB hFiltered E c hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered (Cardinal.lift.{u + 1} μ)
      ((SSet.uliftFunctor.{u + 1, u}).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaFiltered_ulift B
  have hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction ((SSet.uliftFunctor.{u + 2, u + 1}).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).op)
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone a c)) := by
    rintro ⟨k⟩
    obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_right_isColimit a c k (hD k B E c hc)
  have hfull := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimit_of_cardinalExchange
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinalFilteredLimitExchangeShape_ulift_poset_op.{u, u + 1} h I hI)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableFamily a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_inner_isLimit a ha) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone a c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_vertex_isLimit a ha c) hr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_apex_isColimit a c hfull

/-- 元の κ-compact な全項の同じ μ-small poset 余極限は、μ-compact になる。 -/
lemma isMuCompact_smallPosetColimit_of_kappaCompact
    (hD : ∀ k : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ a.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isMuCompact_smallPosetColimit h I hI a ha (fun k ↦ (hD k).of_le h.le)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
