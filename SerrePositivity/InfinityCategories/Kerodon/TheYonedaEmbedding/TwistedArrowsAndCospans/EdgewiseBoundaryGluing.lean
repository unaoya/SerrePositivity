module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightBoundaryCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RangeCoverGluing

/-!
概要：edgewise の境界面と固定した右半分の図式の像の和上での接合。
方針：被覆を Option 型でまとめ、面同士および面と右半分の整合性を使う。
規約：全体の次数は n+2。一次元の境界は別に扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、Kan 延長の入力となる図式の構成。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：右半分と各境界面の被覆射の始域。
方針：none は右標準単体、some i は一つ低次元の edgewise 重みとする。
規約：被覆の添字は Option(Fin(n+3))。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界接合の族の始域。 -/
def edgewiseBoundaryCoverSource (n : ℕ) : Option (Fin (n + 3)) → SSet.{u}
  | none => Δ[n + 2]
  | some _ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌

/-- 概要：右半分と各境界面から全重みへの被覆射の族。
方針：none には右包含、some i には i 面の重みの射を使う。
規約：全体は n+2 次の重み。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、実際の接合領域を像の和で指定する。 -/
def edgewiseBoundaryCoverMap (n : ℕ) : ∀ i, edgewiseBoundaryCoverSource.{u} n i ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 2⦌
  | none => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 2] : SSet.{u}).op Δ[n + 2]
  | some i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)

/-- 概要：右半分と各境界面で指定された図式の族。
方針：右半分では底の図式を使い、各面では境界の単体を Yoneda 表示する。
規約：境界正方形の可換性はこの定義自体には不要。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、被覆上で接合するデータ。 -/
def edgewiseBoundaryCoverDiagram {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K) : ∀ i, edgewiseBoundaryCoverSource n i ⟶ K
  | none => b
  | some i => SSet.yonedaEquiv (boundary.ι i ≫ a)

/-- 概要：可換な境界正方形から得る被覆の図式は像の共通部分で一致する。
方針：右半分同士、右半分と面、面同士の三種類に分け、既存の一致の補題を使う。
規約：全体の次数は二以上。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、像の和の接合補題の整合性条件。 -/
lemma edgewiseBoundaryCover_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 2)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) b)
    (i j : Option (Fin (n + 3))) (d : SimplexCategoryᵒᵖ)
    (x : (edgewiseBoundaryCoverSource n i).obj d) (y : (edgewiseBoundaryCoverSource n j).obj d)
    (hxy : (edgewiseBoundaryCoverMap n i).app d x = (edgewiseBoundaryCoverMap n j).app d y) :
    (edgewiseBoundaryCoverDiagram a b i).app d x = (edgewiseBoundaryCoverDiagram a b j).app d y := by
  cases i with
  | none =>
    cases j with
    | none =>
      have he : x = y := (mono_iff_injective
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 2] : SSet.{u}).op Δ[n + 2]).app d)).mp inferInstance hxy
      subst y
      rfl
    | some j => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a b sq j d y x hxy.symm).symm
  | some i =>
    cases j with
    | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a b sq i d x y hxy
    | some j => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFaces_compatible a i j d x y hxy

/-- 概要：右半分と各境界面の像の和上へ、指定された図式を接合できる。
方針：像の共通部分での一致を被覆の接合補題へ適用する。
規約：ここでは像の和上の射を構成し、全重みへの延長は別に行う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の正次元の境界充填の入力。 -/
lemma exists_edgewiseBoundaryCover_gluing {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 2)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) b) :
    ∃ F : ((⨆ i, Subcomplex.range (edgewiseBoundaryCoverMap n i) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 2⦌).Subcomplex) : SSet.{u}) ⟶ K,
      ∀ i, Subcomplex.lift (edgewiseBoundaryCoverMap n i)
        (le_iSup (fun j ↦ Subcomplex.range (edgewiseBoundaryCoverMap n j)) i) ≫ F =
          edgewiseBoundaryCoverDiagram a b i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_map_of_compatible_range_cover (edgewiseBoundaryCoverSource n)
    (edgewiseBoundaryCoverMap n) (edgewiseBoundaryCoverDiagram a b)
    (edgewiseBoundaryCover_compatible a b sq)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
