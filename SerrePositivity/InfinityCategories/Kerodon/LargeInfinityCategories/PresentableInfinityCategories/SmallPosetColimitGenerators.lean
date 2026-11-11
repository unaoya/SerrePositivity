module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCodes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPartialPresentation

/-!
概要：元の小さい生成圏の μ-small な図式から、共通の小さい μ-compact 対象族を選ぶ。
方針：全図式の符号型を添字とし、指定された native 余極限の存在から一つずつ選ぶ。
規約：任意の元の部分余極限と、選んだ同じ図式の余極限との頂点同型を提供する。
使われ方：濃度変更の対象に依存しない小さい生成圏への入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SmallPosetDiagramCode
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}}
  {C : SSet.{u + 1}}

/-- 符号化された同じ全図式を、元の大きい標的へ合成する。 -/
def realizedDiagram (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve q.Index) ⟶ C :=
  (SSet.uliftFunctor.{u + 1, u}).map q.map ≫ i

/-- 共通の小さい符号型の各図式について、元の標的内の native な余極限を選ぶ。 -/
def colimitCone (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q.realizedDiagram i) := by
  have := q.nerve_isKappaFiltered
  exact (hC (nerve q.Index) (q.realizedDiagram i)).choose

/-- 選んだ全余錐自身が、同じ元の図式の余極限。 -/
lemma colimitCone_isColimit (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (q.colimitCone hC i) := by
  have := q.nerve_isKappaFiltered
  exact (hC (nerve q.Index) (q.realizedDiagram i)).choose_spec

/-- 対象に依存しない小さい符号型で添字づけられた、選択余極限の頂点族。 -/
def vertex (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) : C _⦋0⦌ := (q.colimitCone hC i).vertex

/-- 元の小さい生成族が κ-compact なら、共通の小さい頂点族は μ-compact。 -/
lemma vertex_isMuCompact [Quasicategory C] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (hi : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (i.app _ (ULift.up a)))
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.vertex hC i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isMuCompact_smallPosetColimit_of_kappaCompact h q.Index q.small
    (q.colimitCone hC i) (q.colimitCone_isColimit hC i)
  rintro ⟨j⟩
  exact hi (q.map.app _ j)

end SmallPosetDiagramCode

/-- 任意の元の小さい部分余極限は、共通の小さい族の一つと頂点同型を持つ。 -/
lemma exists_smallPosetColimitGeneratorIso {κ μ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
    (hI : HasCardinalLT I μ) (p : nerve I ⟶ A)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ i)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.vertex (q.vertex hC i)) := by
  obtain ⟨q, e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallPosetDiagramCode (κ := κ) I hI p
  have he' : e.inv ≫ p = q.map := by rw [← he, Iso.inv_hom_id_assoc]
  let r := (SSet.uliftFunctor.{u + 1, u}).map e.inv
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal r := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso r
  have hc' := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r hr c).mp hc
  have hd : r ≫ ((SSet.uliftFunctor.{u + 1, u}).map p ≫ i) = q.realizedDiagram i := by
    dsimp only [r, SmallPosetDiagramCode.realizedDiagram]
    rw [← Category.assoc, ← Functor.map_comp, he']
  let d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq hd (c.restrict r)
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff hd (c.restrict r)).mp hc'
  have hv : d.vertex = c.vertex := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict]
  refine ⟨q, ?_⟩
  exact ⟨hv ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso d (q.colimitCone hC i) hd' (q.colimitCone_isColimit hC i)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
