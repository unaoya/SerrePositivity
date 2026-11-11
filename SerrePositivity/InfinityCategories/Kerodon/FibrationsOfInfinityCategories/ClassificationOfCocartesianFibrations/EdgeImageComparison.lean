module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ComparisonTriangle

/-!
概要：異なる底を持つ二射の間でも、比較三角形で cocartesian 辺の像を検出する。
方針：同じ始点と底の辺を持つ lift との比較の可逆辺を写し、合成閉性を使う。
規約：比較写像が同じ底上の射であるという余分な条件を課さない。
使われ方：cocartesian fibration の底変換の第一射影が辺を保存することの検証。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ始点・底の lift の像が cocartesian なら、元の cocartesian 辺の像も cocartesian。 -/
lemma isCocartesianEdge_image_of_matching_lift {X E A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (r : X ⟶ A) (p : E ⟶ B)
    [InnerFibration r] [InnerFibration p] (f : X ⟶ E)
    (e h : X _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge r e) (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge r h)
    (hs : X.δ 1 h = X.δ 1 e) (hr : r.app (Opposite.op ⦋1⦌) h = r.app _ e)
    (hfh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) e) := by
  let : Quasicategory X := quasicategory_of_innerFibration r
  let : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨t, ht₂, ht₁, hi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianComparisonTriangle r e h he hh hs hr
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ (t ≫ f))) := by
    rw [← Category.assoc, ht₂, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hfh
  have hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ (t ≫ f))) := by
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_isInvertibleEdge p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t))).map ((truncation 2).map f))
      (hi.map f)
  have hlong := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge (t ≫ f) p hfirst hsecond
  rw [← Category.assoc, ht₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hlong
  exact hlong

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
