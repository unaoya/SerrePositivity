module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceLocalTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EmptyShapeConeCriterion

/-!
概要：固定始域圏の accessibility が得られれば、その終対象と局所置換を構成できる。
方針：証明済みの小余完備性と合わせて presentable にし、空極限を取る。
規約：固定始域圏の accessibility は未解決の入力として明示する。
使われ方：e5 の filtered 生成表示の供給後に接続する f3 の存在部分。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 未解決の accessibility を明示すると、固定始域圏の presentable 性が従う。 -/
lemma generatedSource_isPresentable_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) :=
  ⟨ha, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_hasSmallColimits hC edges x⟩

/-- 固定始域圏の accessibility が得られれば、同じ圏に実際の終対象が存在する。 -/
lemma exists_generatedSource_terminal_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x)) :
    ∃ s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex s := by
  let K := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).toSSet
  let L := (SSet.uliftFunctor.{u + 1, u}).obj K
  have hL : ¬ L.Nonempty := by
    rintro ⟨v⟩
    exact v.down.property
  let p : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x := (SSet.isInitialOfNotNonempty hL).to _
  obtain ⟨c, hc⟩ :=
    (generatedSource_isPresentable_of_isAccessible hC edges x ha).hasLimit p
  exact ⟨c.vertex, (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_emptyShape_iff_vertex hL c).mp hc⟩

/-- 同じ accessibility の入口だけを残し、元の始点から閉包内の局所置換を得る。 -/
lemma exists_generatedSource_localReplacement_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x)) :
    ∃ (y : C _⦋0⦌) (e : C.Edge x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) y := by
  obtain ⟨s, hs⟩ := exists_generatedSource_terminal_of_isAccessible hC edges x ha
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceTarget edges x).app _ s,
    SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceLeg edges x s), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceLeg_mem edges x s,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_terminal_target_isLocalObject hC edges x s hs⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
