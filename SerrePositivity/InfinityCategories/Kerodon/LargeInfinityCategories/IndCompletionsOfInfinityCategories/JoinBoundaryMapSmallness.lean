module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FixedVertexMapSmallness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSmallness

/-!
概要：join の両側への制限を固定した全写像の型は小さい。
方針：両包含が全頂点を覆うので、固定頂点写像の型へ単射に入れる。
規約：全射を保持。使われ方：図式 comma の各単体の小ささ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- join の両端を固定した全写像は小さい。 -/
lemma small_joinMaps_fixedBoundary {A B Y : SSet.{u + 1}}
    [∀ n, Small.{u} (A.obj n)] [∀ n, Small.{u} (B.obj n)]
    (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps Y) (p : A ⟶ Y) (q : B ⟶ Y) :
    Small.{u} {f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ Y // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = q} := by
  classical
  let T := {f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ Y // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = q}
  by_cases h : Nonempty T
  · obtain ⟨f₀⟩ := h
    let v := fun a => f₀.val.app (Opposite.op ⦋0⦌) a
    haveI := hY (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) (fun n => inferInstance) v
    let code (f : T) :
        {g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ Y // ∀ a, g.app (Opposite.op ⦋0⦌) a = v a} :=
      ⟨f.val, by
        intro a
        rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertices_covered A B a with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f.val).app _ b = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f₀.val).app _ b
          rw [f.property.1, f₀.property.1]
        · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f.val).app _ b = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f₀.val).app _ b
          rw [f.property.2, f₀.property.2]⟩
    apply small_of_injective (f := code)
    intro f g he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · haveI : IsEmpty T := ⟨fun f => h ⟨f⟩⟩
    exact inferInstanceAs (Small.{u} T)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
