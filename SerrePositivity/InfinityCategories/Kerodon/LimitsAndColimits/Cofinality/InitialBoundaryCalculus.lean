module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-!
概要：相対始点境界充填の合成と底変換。
方針：合成では二段階に充填し、引き戻しでは指定された底の単体と充填を合わせる。
規約：全ての射は任意で、fibration 性や quasicategory 性を仮定しない。
使われ方：相対余錐の充填条件と絶対的な余極限性を接続する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：相対始点境界充填は二つの射の合成で保たれる。
方針：像の境界を後半の射で充填し、その指定充填の上で元の境界を充填する。
規約：二つの射の充填性をそれぞれの始点で要求する。
使われ方：相対余錐制限と底の余錐制限の普遍性の合成。 -/
lemma initialBoundaryLifting_comp {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (x : X _⦋0⦌) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting q (p.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (p ≫ q) x := by
  intro n a b ha sq
  have ha' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  have sq' : CommSq (a ≫ p) (boundary (n + 1)).ι q b := by
    constructor
    rw [Category.assoc]
    exact sq.w
  obtain ⟨g, hg, hgq⟩ := hq n (a ≫ p) b ha' sq'
  obtain ⟨F, hF, hFp⟩ := hp n a g ha ⟨hg.symm⟩
  refine ⟨F, hF, ?_⟩
  rw [← Category.assoc, hFp, hgq]

/-- 概要：相対始点境界充填は任意の底変換で保たれる。
方針：第二成分を充填し、指定された第一成分と引き戻しへ合わせる。
規約：引き戻しの頂点の第二成分で元の条件を要求する。
使われ方：標的の余極限余錐の普遍性を相対余錐の標的へ移す。 -/
lemma initialBoundaryLifting_pullback_fst {X E B : SSet.{u}}
    (f : X ⟶ B) (p : E ⟶ B) (x : (pullback f p) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p ((pullback.snd f p).app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (pullback.fst f p) x := by
  intro n a b ha sq
  have ha' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ pullback.snd f p) =
      SSet.yonedaEquiv.symm ((pullback.snd f p).app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  have sq' : CommSq (a ≫ pullback.snd f p) (boundary (n + 1)).ι p (b ≫ f) := by
    constructor
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := hx n (a ≫ pullback.snd f p) (b ≫ f) ha' sq'
  refine ⟨pullback.lift b F hFp.symm, ?_, pullback.lift_fst _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact sq.w.symm
  · rw [Category.assoc, pullback.lift_snd]
    exact hF

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
