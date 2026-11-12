module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：単体的に豊穣な終対象を coherent nerve の終対象として検出する。
方針：豊穣 Hom の終対象性を宇宙の持ち上げで可縮性に移し、F1 の写像空間比較と A3d を使う。
規約：単体的圏は局所 Kan。対象と Hom の宇宙は異なってよい。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の空積の場合。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：終対象である単体集合の宇宙を持ち上げると可縮な Kan 複体。
方針：終対象性から各次数の一意性を得て、選んだ頂点への定値射で全境界を充填する。
規約：持ち上げる宇宙 v は任意であり、異なる宇宙間の射は使わない。
使われ方：Kerodon 4.6.7.5（Tag 01LE）、7.5.4.6（Tag 03BB） の終対象の写像空間。 -/
lemma ulift_isContractibleKan_of_isTerminal (K : SSet.{u}) (hK : IsTerminal K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (SSet.uliftFunctor.{v, u}.obj K) := by
  let x : K _⦋0⦌ := SSet.yonedaEquiv (hK.from (Δ[0] : SSet.{u}))
  have hs (n : SimplexCategoryᵒᵖ) : Subsingleton (K.obj n) := by
    obtain ⟨⟨n⟩⟩ := n
    exact ⟨fun _ _ ↦ SSet.yonedaEquiv.symm.injective (hK.hom_ext _ _)⟩
  intro n b
  refine ⟨SSet.const (ULift.up x), ?_⟩
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact (hs m).elim _ _

/-- 概要：全ての sHom(x,t) が単体集合の終対象なら t は coherent nerve の終対象。
方針：任意の頂点を元の対象で表示し、Hom の可縮性を標準の写像空間比較で移して A3d を使う。
規約：局所 Kan 性と豊穣終対象性を前提にし、追加の錐の比較を仮定しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の空積への適用。 -/
lemma coherentNerve_isTerminalVertex_of_enrichedTerminal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ x y : C, KanComplex (SimplicialCategory.sHom x y)]
    (t : C) (h : ∀ x : C, IsTerminal (SimplicialCategory.sHom x t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).surjective z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence x t).isContractibleKan
    (ulift_isContractibleKan_of_isTerminal _ (h x))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
