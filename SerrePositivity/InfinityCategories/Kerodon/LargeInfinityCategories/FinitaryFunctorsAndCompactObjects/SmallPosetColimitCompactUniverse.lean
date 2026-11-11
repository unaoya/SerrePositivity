module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalExchangeReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ColimitClosureExchange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Aleph0CardinalChangeBound

/-!
概要：小さい poset 上の μ-compact 対象の指定余極限頂点は、同じ μ に関して compact。
方針：同じ Hom 全錐族の宇宙へ実証済み交換を移し、元の全余錐の全評価を反映する。
規約：C と指定余極限は max u v、試験添字と κ・μ は u。交換を instance で補わない。
使われ方：κ-compact な生成図式の μ-small 部分余極限の μ-compact 性。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

section
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
  {C : SSet.{max u v}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ C}
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a)

include h hI ha

/-- 概要：小さい poset 上の μ-compact 頂点の指定余極限も μ-compact。
方針：宇宙を分離した全 Hom 錐族に、持ち上げた poset の交換を適用する。
規約：添字と濃度は u、標的は max u v とする。
使われ方：D-8 の大きい圏の小余極限閉性。 -/
lemma isMuCompact_smallPosetColimit_universe
    (hD : ∀ k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} μ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} μ a.vertex := by
  intro B hB hFiltered E c hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered (Cardinal.lift.{v} μ)
      ((SSet.uliftFunctor.{v, u}).obj B) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaFiltered_ulift B
  have hr : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction ((SSet.uliftFunctor.{max u v + 1, max u v}).obj
        ((SSet.uliftFunctor.{v, u}).obj (nerve I)).op)
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone a c)) := by
    rintro ⟨k⟩
    obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_right_isColimit a c k (hD k B E c hc)
  have hfull := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimit_of_cardinalExchange
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.cardinalFilteredLimitExchangeShape_ulift_poset_op.{u, v} h I hI)
    ((SSet.uliftFunctor.{max u v + 1, max u v}).map E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitRepresentableFamily a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_inner_isLimit a ha) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone a c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_vertex_isLimit a ha c) hr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homConeCocone_apex_isColimit a c hfull

/-- 概要：κ-compact 頂点の μ-small poset 余極限は μ-compact。
方針：κ ≤ μ による compact 性の移送後に同じ余錐を評価する。
規約：元の余極限頂点を保持する。
使われ方：濃度を拡大した生成表示の部分余極限。 -/
lemma isMuCompact_smallPosetColimit_universe_of_kappaCompact
    (hD : ∀ k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} μ a.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isMuCompact_smallPosetColimit_universe h I hI a ha (fun k ↦ (hD k).of_le h.le)

end

/-- 概要：非可算正則 μ の compact 頂点は、μ-small poset 余極限で閉じる。
方針：ℵ₀ から μ への濃度変更評価を、同じ余錐の compact 判定へ代入する。
規約：離散 poset を含み、濃度や試験添字の宇宙を変更しない。
使われ方：D-8 の κ-small な余積と poset 余極限。 -/
lemma isKappaCompact_smallPosetColimit_universe
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    {C : SSet.{max u v}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a)
    (hD : ∀ k : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} μ (D.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} μ a.vertex := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact isMuCompact_smallPosetColimit_universe (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalChangeBound_aleph0 hμ) I hI a ha hD

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
