module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：cocartesian な辺の引き戻し。
方針：元の相対外側ホーンを充填し、指定された基底の単体と pullback で合わせる。
規約：quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9）、§7.1.8（Tag 02X8） の図式に沿う錐の輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：引き戻しの辺が元の射に対して cocartesian へ写れば、その辺は第二射影に対して cocartesian。
方針：元の相対外側ホーンを充填し、標的の単体と合わせる。
規約：ファイブレーション性・quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の cocartesian な辺の基底変換。 -/
lemma hasCocartesianHornLifting_pullback_of_fst {E B A : SSet.{u}} (p : E ⟶ B) (f : A ⟶ B)
    {x y : (pullback p f) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (pullback p f)) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (e.map ((truncation 2).map (pullback.fst p f)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting (pullback.snd p f) e := by
  intro n σ β hσ hw
  have hfirst : (σ ≫ pullback.fst p f).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
      (e.map ((truncation 2).map (pullback.fst p f))).edge :=
    congrArg ((pullback.fst p f).app (Opposite.op ⦋1⦌)) hσ
  have hs : (σ ≫ pullback.fst p f) ≫ p = (horn (n + 2) 0).ι ≫ (β ≫ f) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := he n (σ ≫ pullback.fst p f) (β ≫ f) hfirst hs
  refine ⟨pullback.lift F β hFp, ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hF]
  · rw [Category.assoc, pullback.lift_snd, hw]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
