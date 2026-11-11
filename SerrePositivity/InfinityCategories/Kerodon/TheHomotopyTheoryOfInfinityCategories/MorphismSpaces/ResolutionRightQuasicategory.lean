module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionMonomorphisms

/-!
概要：解像による同値の保存と右随伴の quasicategory 性。
方針：一般の射影の自然性で同値を移し、単射な同値上の延長を随伴で内ホーンの充填へ戻す。
規約：単体集合の圏での随伴とホーンの充填だけを使う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、Theorem 4.6.7.5（Tag 01LE）、右随伴の比較の準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：解像関手は前合成による同値を保存する。
方針：一般の射影の自然性の正方形で二対三則を使う。
規約：元の二つの単体集合に quasicategory 性は要求しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、解像した内ホーンの同値性。 -/
lemma coherentResolution_map_isPrecompositionEquivalence {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map f) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence A).comp hf
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app A ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality f
  rw [← hn] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence B).cancel_right h

/-- 概要：単射で前合成による同値となる射の上で関手を厳密に延長できる。
方針：前合成の本質的全射性を頂点全射性へ厳密化して使う。
規約：標的だけが quasicategory であればよい。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM）、Proposition 4.6.7.23（Tag 01LW）、解像したホーンの延長。 -/
lemma exists_extension_of_precompositionEquivalence {A B Z : SSet.{u}} [Quasicategory Z]
    (i : A ⟶ B) [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (a : A ⟶ Z) :
    ∃ b : B ⟶ Z, i ≫ b = a := by
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pre_surjective_of_essentiallySurjective i (hi Z).choose.isEssentiallySurjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B Z).surjective v
  refine ⟨b, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective ?_⟩
  exact hv

/-- 概要：解像の右随伴は quasicategory を quasicategory に写す。
方針：内ホーンを随伴で解像後の延長問題に移し、単射と同値の保存で延長する。
規約：Kan 性を仮定せずに内ホーンのみを充填する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Proposition 4.6.7.23（Tag 01LW）、右随伴による写像空間の表示。 -/
instance coherentResolutionRightAdjoint_quasicategory (Z : SSet.{u}) [Quasicategory Z] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) where
  hornFilling' {n i} σ h₀ hlast := by
    let j := (horn (n + 2) i).ι
    haveI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map_mono j
    have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j) :=
      coherentResolution_map_isPrecompositionEquivalence j
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne j
          (innerAnodyneExtensions.horn_ι h₀ hlast))
    obtain ⟨g, hg⟩ := exists_extension_of_precompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j) hj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z).symm σ)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z g, ?_⟩
    have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z) hg
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] at h
    exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
