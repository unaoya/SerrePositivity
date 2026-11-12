module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.JoinMapRange
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftGluing
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：edgewise の重みの境界面の像。
方針：join の射の像を左右の像に分解し、標準単体の面の像と反転の像を使う。
規約：同じ面の添字を両因子へ適用する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界図式を重みの部分複体へ接合する入力。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の面の像は、左右の同じ添字の面の像を両方満たす部分複体。
方針：標準単体の面の像の式と反転の像の式を join の像の計算へ適用する。
規約：左因子の面は反転した部分複体として指定する。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、境界面の像を共通部分で表す。 -/
lemma edgewiseWeight_face_range (n : ℕ) (i : Fin (n + 2)) :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (stdSimplex.face ({i}ᶜ)).op Δ[n + 1] ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight (Δ[n + 1] : SSet.{u}).op (stdSimplex.face ({i}ᶜ)) := by
  change Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.δ i)) (stdSimplex.δ i)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinMap_range, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.subcomplex_range_opFunctor_map, stdSimplex.range_δ]

/-- 概要：edgewise の境界面からの重みの射は単射。
方針：標準単体の面の単射性、反転での保存、join での保存を使う。
規約：同じ単体に二つの異なる面の像が重なることは許す。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、各面の図式をその像へ運ぶための同型。 -/
instance edgewiseWeight_face_mono (n : ℕ) (i : Fin (n + 2)) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)) := by
  letI : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.δ i)) (stdSimplex.δ i))
  infer_instance

/-- 概要：二つの edgewise の境界面の像の共通部分は、左右の共通面を同時に満たす部分複体。
方針：各面の像の式と join による共通部分の保存を使う。
規約：同じ面の添字 i=j の場合も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、異なる面から運んだ図式の一致を確認する領域。 -/
lemma edgewiseWeight_face_range_inf (n : ℕ) (i j : Fin (n + 2)) :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ i)) ⊓
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft ((stdSimplex.face ({i}ᶜ) ⊓ stdSimplex.face ({j}ᶜ)).op) Δ[n + 1] ⊓
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight (Δ[n + 1] : SSet.{u}).op
        (stdSimplex.face ({i}ᶜ) ⊓ stdSimplex.face ({j}ᶜ)) := by
  rw [edgewiseWeight_face_range, edgewiseWeight_face_range]
  have hop : (stdSimplex.face ({i}ᶜ) ⊓ stdSimplex.face ({j}ᶜ)).op =
      (stdSimplex.face ({i}ᶜ)).op ⊓ (stdSimplex.face ({j}ᶜ)).op := by
    ext d s
    rfl
  rw [hop, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft_inf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight_inf]
  ac_rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
