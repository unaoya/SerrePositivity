module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-!
概要：引き戻しの第一射影に関する cartesian 輸送。
方針：第二成分の輸送を指定された第一成分と合わせる。
規約：元の cartesian fibration は引き戻しの第二の構造射に置く。
使われ方：相対余錐制限の標的の図式への射影。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：引き戻しの辺の第二成分が cartesian なら第一射影に関して cartesian。
方針：第二成分の外側ホーンを持ち上げ、指定された第一成分と引き戻しへ合わせる。
規約：構造射に充填性は仮定しない。
使われ方：相対余錐制限の像の cartesian 性の判定。 -/
lemma isCartesianEdge_pullback_fst {X Y B : SSet.{u}} (f : X ⟶ B) (p : Y ⟶ B)
    (e : (pullback f p) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p ((pullback.snd f p).app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (pullback.fst f p) e := by
  intro n a b ha sq
  have sq' : CommSq (a ≫ pullback.snd f p)
      (horn (n + 2) (Fin.last (n + 2))).ι p (b ≫ f) := by
    constructor
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, sq.w, Category.assoc]
  have := he n (a ≫ pullback.snd f p) (b ≫ f)
    (by change (pullback.snd f p).app _ (a.app _ _) = _; rw [ha]) sq'
  refine CommSq.HasLift.mk' {
    l := pullback.lift b sq'.lift sq'.fac_right.symm
    fac_left := ?_
    fac_right := pullback.lift_fst _ _ _ }
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using sq.w.symm
  · simpa only [Category.assoc, pullback.lift_snd] using sq'.fac_left

/-- 概要：cartesian fibration を第二の構造射とする引き戻しの第一射影は cartesian。
方針：引き戻しの対称同型を通常の底変換に合成する。
規約：底変換の射 f は任意。
使われ方：元の図式へ射影する相対余錐の標的の構造。 -/
instance cartesianFibration_pullback_fst {X Y B : SSet.{u}} (f : X ⟶ B) (p : Y ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.fst f p) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullbackSymmetry f p).hom :=
    ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations (pullbackSymmetry f p).hom⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
      ((pullbackSymmetry f p).hom ≫ pullback.snd p f) := inferInstance
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
