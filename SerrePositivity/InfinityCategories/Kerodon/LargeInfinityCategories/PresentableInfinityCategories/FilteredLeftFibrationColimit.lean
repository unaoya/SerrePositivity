module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：底上の left fibrations の通常の filtered 余極限も left fibration である。
方針：底上の有限ホーンを元の同じ余錐の一段へ因子化し、その段の充填を余極限へ送る。
規約：任意の指定余錐と全脚を保持する。底の quasicategory 性は仮定しない。
使われ方：有限底上模型の全表示を left fibrations の ∞ 圏へ移す準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 任意の指定された底上の filtered 余極限の射影は、各段が left fibration なら同じ性質を持つ。 -/
lemma leftFibration_of_filtered_isColimit {B : SSet.{u}}
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Over B) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (F.obj j).hom) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration c.pt.hom where
  mem := by
    intro A D i hi
    cases hi with
    | @intro n i hi =>
      constructor
      intro a b sq
      let T : Over B := Over.mk ((horn (n + 1) i).ι ≫ b)
      have : T.left.Finite := by
        change (horn (n + 1) i : SSet.{u}).Finite
        infer_instance
      have : IsFinitelyPresentable.{u} T := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentable.finiteOver_isFinitelyPresentable T.hom
      let t : T ⟶ c.pt := Over.homMk a sq.w
      obtain ⟨j, s, hs⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc t
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (F.obj j).hom := hF j
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := (F.obj j).hom) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
      let q : CommSq s.left (horn (n + 1) i).ι (F.obj j).hom b := ⟨s.w⟩
      refine CommSq.HasLift.mk' { l := q.lift ≫ (c.ι.app j).left, fac_left := ?_, fac_right := ?_ }
      · rw [← Category.assoc, q.fac_left]
        exact congrArg (fun k ↦ k.left) hs
      · have hleg : (c.ι.app j).left ≫ c.pt.hom = (F.obj j).hom := (c.ι.app j).w
        rw [Category.assoc, hleg, q.fac_right]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
