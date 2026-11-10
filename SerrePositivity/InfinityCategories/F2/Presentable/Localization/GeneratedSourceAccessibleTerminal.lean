module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceLocalTerminal
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.EmptyShapeConeCriterion

/-!
概要：固定始域圏の accessibility が得られれば、その終対象と局所置換を構成できる。
方針：証明済みの小余完備性と合わせて presentable にし、空極限を取る。
規約：固定始域圏の accessibility は未解決の入力として明示する。
使われ方：e5 の filtered 生成表示の供給後に接続する f3 の存在部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 未解決の accessibility を明示すると、固定始域圏の presentable 性が従う。 -/
lemma generatedSource_isPresentable_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : IsAccessible (generatedSourceCategory edges x)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (generatedSourceCategory edges x) :=
  ⟨ha, generatedSource_hasSmallColimits hC edges x⟩

/-- 固定始域圏の accessibility が得られれば、同じ圏に実際の終対象が存在する。 -/
lemma exists_generatedSource_terminal_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : IsAccessible (generatedSourceCategory edges x)) :
    ∃ s : (generatedSourceCategory edges x) _⦋0⦌, IsTerminalVertex s := by
  let K := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).toSSet
  let L := (SSet.uliftFunctor.{u + 1, u}).obj K
  have hL : ¬ L.Nonempty := by
    rintro ⟨v⟩
    exact v.down.property
  let p : L ⟶ generatedSourceCategory edges x := (SSet.isInitialOfNotNonempty hL).to _
  obtain ⟨c, hc⟩ :=
    (generatedSource_isPresentable_of_isAccessible hC edges x ha).hasLimit p
  exact ⟨c.vertex, (F2.isLimitCone_emptyShape_iff_vertex hL c).mp hc⟩

/-- 同じ accessibility の入口だけを残し、元の始点から閉包内の局所置換を得る。 -/
lemma exists_generatedSource_localReplacement_of_isAccessible
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (ha : IsAccessible (generatedSourceCategory edges x)) :
    ∃ (y : C _⦋0⦌) (e : C.Edge x y),
      e.edge ∈ generatedEdges edges ∧ IsLocalObject (Set.range edges) y := by
  obtain ⟨s, hs⟩ := exists_generatedSource_terminal_of_isAccessible hC edges x ha
  exact ⟨(generatedSourceTarget edges x).app _ s,
    SSet.Edge.ofTruncated (generatedSourceLeg edges x s), generatedSourceLeg_mem edges x s,
    generatedSource_terminal_target_isLocalObject hC edges x s hs⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
