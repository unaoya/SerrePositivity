module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomCartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FinalHornPullbackExtension

/-!
概要：任意の pullback 表示で、quasicategory の底上の cocartesian 辺の像を比較する。
方針：標準 pullback への同型と元の第一射影の辺の保存を使う。
規約：全空間の表示を選び直した後も、元の辺の像そのものを結論する。
使われ方：一辺への制限を経由する、任意の単体集合への底変換の照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- quasicategory の底への任意の pullback 表示の上の cocartesian 辺は元の全空間でも cocartesian。 -/
lemma isCocartesianEdge_image_of_isPullback_of_quasicategory_base
    {P E A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {i : P ⟶ E} {r : P ⟶ A} {f : A ⟶ B}
    (hs : IsPullback i r p f) (e : P _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge r e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌) e) := by
  let k := hs.isoPullback
  have hk : k.hom ≫ pullback.snd p f = r := hs.isoPullback_hom_snd
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (k.hom ≫ pullback.snd p f) e := by
    rw [hk]
    exact he
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_map_iso k (pullback.snd p f) e he'
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_pullback_image_of_quasicategory_base p f
    (k.hom.app (Opposite.op ⦋1⦌) e) hc
  have hfst : (pullback.fst p f).app (Opposite.op ⦋1⦌)
      (k.hom.app (Opposite.op ⦋1⦌) e) = i.app (Opposite.op ⦋1⦌) e :=
    congrArg (fun m ↦ m.app (Opposite.op ⦋1⦌) e) hs.isoPullback_hom_fst
  rwa [hfst] at h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
