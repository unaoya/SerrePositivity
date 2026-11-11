module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinEndpointPullbacks

/-!
概要：edgewise の境界面の図式と固定した右半分の図式の一致。
方針：右端射影の評価を Yoneda 表示で計算し、join の右包含の pullback で共通単体を比較する。
規約：任意の正次元の境界を扱い、標的の Kan 性は不要。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界面と右半分を同時に接合する条件。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の標準単体の右射影による像は、重みの右半分への制限と一致する。
方針：Yoneda の同値で射を比較し、右射影の成分の定義を使う。
規約：任意の次数 n の単体を扱う。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、右半分の図式との比較。 -/
lemma edgewiseRight_yoneda {K : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K := by
  apply SSet.yonedaEquiv.injective
  erw [SSet.yonedaEquiv_comp f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K)]

/-- 概要：可換な右射影の境界正方形では、面の図式の右半分は指定した底の面になる。
方針：右射影の Yoneda 計算と境界正方形の可換性を各面で使う。
規約：全体の次数は n+1。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、面と右半分の接合の元の等式。 -/
lemma edgewiseBoundaryFace_right_restriction {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) b) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv (boundary.ι i ≫ a) =
      stdSimplex.δ i ≫ b := by
  rw [edgewiseRight_yoneda, Category.assoc, sq.w, ← Category.assoc, boundary.ι_ι]

/-- 概要：境界面と右半分が同じ重みの単体を表すとき、指定した図式の値は一致する。
方針：右包含と面の重みの pullback で共通の単体を取り、右半分への制限の式を評価する。
規約：任意の単体次数 d を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、面の像と右半分の像の接合の整合性。 -/
lemma edgewiseBoundaryFace_right_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) b)
    (i : Fin (n + 2)) (d : SimplexCategoryᵒᵖ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌).obj d) (y : (Δ[n + 1] : SSet.{u}).obj d)
    (hxy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x = b.app d y := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_joinInr_naturality
    (SSet.opFunctor.map (stdSimplex.{u}.δ i)) (stdSimplex.δ i)
  obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback (hp.app d) x y hxy
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (edgewiseBoundaryFace_right_restriction a b sq i) d) z
  change (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}).op Δ[n]).app d z) =
    b.app d ((stdSimplex.δ i).app d z) at h
  rw [hzx, hzy] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
