module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite

/-!
概要：弱可縮な形状から一点への射は right cofinal。
方針：一点上の coslice 射影が厳密な同型であることを用いて Quillen A を適用する。
規約：元の形状の quasicategory 性は不要。
使われ方：sifted 形状上の定値図式の余極限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：一点を標的とする図式の coslice 射影は同型。
方針：各単体の元の射が終対象への唯一の射であることを使う。
規約：元の図式を固定する。
使われ方：一点への射の coslice の同定。 -/
lemma sliceUnder_point_projection_isIso {J : SSet.{u}} (p : J ⟶ (Δ[0] : SSet.{u})) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) := by
  have hs (n : SimplexCategoryᵒᵖ) : Subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).obj n) := by
    refine ⟨fun a b ↦ Subtype.ext (stdSimplex.isTerminalObj₀.hom_ext a.val b.val)⟩
  have hn (n : SimplexCategoryᵒᵖ) : Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).obj n) :=
    ⟨⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · exact fun _ _ _ ↦ (hs n).elim _ _
  · intro a
    obtain ⟨b⟩ := hn n
    refine ⟨b, ?_⟩
    rcases n with ⟨⟨m⟩⟩
    apply SSet.yonedaEquiv.symm.injective
    exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：弱可縮な元の形状から一点への射は right cofinal。
方針：各 coslice の同型な射影で弱可縮性を移して Quillen A を使う。
規約：元の形状に充填性を要求しない。
使われ方：定値図式の元の余極限の判定。 -/
lemma pointProjection_isRightCofinal {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (stdSimplex.isTerminalObj₀.from K) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro b
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b)) :=
    sliceUnder_point_projection_isIso _
  let r := pullback.fst (stdSimplex.isTerminalObj₀.from K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b))
  have hw := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso r).isWeakHomotopyEquivalence
  exact hw.weaklyContractible_iff.mpr hK

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
