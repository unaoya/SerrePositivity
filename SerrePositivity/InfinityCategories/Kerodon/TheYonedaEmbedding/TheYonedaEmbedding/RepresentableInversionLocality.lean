module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableInversionTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PinchedPrecompositionPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PinchedSliceTransportReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity

/-!
概要：元の表現可能前層が反対辺を反転するなら、同じ元の Hom 前合成は同値である。
方針：分類辺の反転から元の slice 輸送の同値性を得て、指定全底の前合成円柱で戻す。
規約：P 所有の局所性述語を import せず、その本体と同じ型の一方向を公開する。
使われ方：Ind-S の前層 ∞ 圏での RepresentableInversionDetectsLocality の充足。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
/-- 概要：同じ表現可能前層の反対辺像の可逆性は、元の Hom 前合成の同値性を与える。
方針：元の分類輸送と実前合成円柱。規約：元の辺。使われ方：局所性の判定。 -/
lemma representablePresheafInfinity_precompose_isQCatEquivalence_of_invertible
    {C : SSet.{u}} [Quasicategory C] (z : C _⦋0⦌) {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose z (Truncated.HomotopyCategory.homMk e)) := by
  obtain ⟨H, h₀, h₁, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pinchedPrecompose_slicePrism_exists z e
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pinchedMap_isQCatEquivalence_of_slicePrism_transport z e _ H h₀ h₁ hp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_transport_of_invertible z e he

/-- 概要：元の前層 ∞ 圏で、表現可能前層の反対辺作用から Hom の局所性を判定する。
方針：一般の元の Hom 判定を適用。規約：同じ全前層。
使われ方：P-1 d の RepresentableInversionDetectsLocality の本体へ直接供給。 -/
lemma presheafInfinity_representableInversion_detects_locality
    {A : SSet.{u}} [Quasicategory A] (z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A _⦋0⦌)
    {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A)) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose z (Truncated.HomotopyCategory.homMk e)) :=
  representablePresheafInfinity_precompose_isQCatEquivalence_of_invertible z e he

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
