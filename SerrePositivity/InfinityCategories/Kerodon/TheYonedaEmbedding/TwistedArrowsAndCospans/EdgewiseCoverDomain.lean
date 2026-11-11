module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFaceDomainCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseBoundaryGluing

/-!
概要：edgewise の境界接合の被覆と Kan 延長領域の同定。
方針：標準単体の右面と二頂点を欠く面の逆像を、それぞれ被覆射の像に置き換える。
規約：被覆の Option 添字の none は右半分。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、接合した図式を Kan 延長定理へ渡す。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：重みの右延長領域は右包含の像と全ての境界面の像の和。
方針：標準単体の延長領域の定義を逆像に移し、各面の逆像の式を使う。
規約：全体の次数は n+1 で、一次元も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、延長領域を実際の境界の被覆で表示する。 -/
lemma edgewiseRightWeightDomain_eq_face_cover (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain.{u} (n + 1) =
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]) ⊔
        ⨆ i : Fin (n + 2), Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)) := by
  change (stdSimplex.face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices (n + 1))).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso (n + 1)).hom ⊔
    (⨆ i : Fin (n + 2), stdSimplex.face
      ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex (n + 1) i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex (n + 1) i}ᶜ)).preimage
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso (n + 1)).hom = _
  rw [Subcomplex.preimage_iSup, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_right_face_preimage]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_pair_face_preimage]

/-- 概要：二次元以上の接合の Option 被覆の像の和は Kan 延長領域そのもの。
方針：右半分と面の和の表示を、Option 型の上限へ組み直す。
規約：全体の次数は n+2。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界接合から全重みへの延長の接続。 -/
lemma edgewiseRightWeightDomain_eq_boundary_cover (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain.{u} (n + 2) =
      ⨆ i, Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryCoverMap.{u} n i) := by
  rw [edgewiseRightWeightDomain_eq_face_cover (n + 1)]
  apply le_antisymm
  · refine sup_le ?_ (iSup_le (fun i ↦ ?_))
    · exact le_iSup (fun j ↦ Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryCoverMap n j)) none
    · exact le_iSup (fun j ↦ Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryCoverMap n j)) (some i)
  · apply iSup_le
    intro i
    cases i with
    | none => exact le_sup_left
    | some i =>
      exact le_trans (le_iSup (fun k : Fin (n + 3) ↦
        Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ k))) i) le_sup_right

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
