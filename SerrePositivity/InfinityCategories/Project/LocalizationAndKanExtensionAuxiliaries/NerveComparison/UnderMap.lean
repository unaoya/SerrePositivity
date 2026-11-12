module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderChain

/-!
概要：Under c の nerve から c 下の native な coslice へ写す。
方針：前置した射列を点と標準単体の join からの射として読む。
規約：同じ宇宙の小さい圏を扱い、始対象性は仮定しない。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Under c の各単体を c 下の coslice の単体へ写す。
方針：前置した射列を Yoneda と join の同型で表示する。
規約：固定した左因子は nervePoint c。
使われ方：native な coslice の比較射。 -/
def nerveUnderSimplex {n : ℕ} (F : ComposableArrows (Under c) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) _⦋n⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c F), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inl_vertex]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact ComposableArrows.ext₀ rfl⟩

/-- 概要：Under c の nerve を c 下の native な coslice へ写す。
方針：単体ごとの表示と join の同型の自然性を合わせる。
規約：quasicategory 性の仮定を追加しない。
使われ方：pointwise Kan の添字圏の比較。 -/
def nerveUnderMap : nerve (Under c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) where
  app _ := ↾fun F ↦ nerveUnderSimplex c F
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := nerve C)).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c ((nerve (Under c)).map α F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α.unop) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := nerve C)).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c F))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain_naturality]
    rfl

/-- 概要：coslice の射影は Under の忘却関手の nerve と一致する。
方針：点との join の右包含が先頭の面であることを使う。
規約：単体集合の射の厳密な等式。
使われ方：Kan の局所図式の射影の照合。 -/
lemma nerveUnderMap_projection : nerveUnderMap c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) =
    nerveMap (Under.forget c) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := nerve C)).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderChain c F))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
