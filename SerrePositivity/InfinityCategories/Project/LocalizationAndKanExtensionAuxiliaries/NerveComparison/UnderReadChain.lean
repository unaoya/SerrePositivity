module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderMap

/-!
概要：c 下の native な coslice の単体を先頭固定の射列として読む。
方針：点と標準単体の join の逆同型と Yoneda を使う。
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

/-- 概要：coslice の単体を通常の圏の長さ n+1 の射列として読む。
方針：join の逆同型に沿う Yoneda 対応を使う。
規約：元の単体の図式を変更しない。
使われ方：Under c の単体への逆写像。 -/
def nerveUnderUnderlyingChain {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) _⦋n⦌) :
    ComposableArrows C (n + 1) :=
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).inv ≫ σ.val)

/-- 概要：読んだ射列を join からの射へ戻すと元の単体になる。
方針：join の同型と Yoneda の逆性を使う。
規約：射の厳密な等式。
使われ方：単体ごとの右逆性。 -/
lemma nerveUnderUnderlyingChain_encode {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (nerveUnderUnderlyingChain c σ) =
      σ.val := by
  simp only [nerveUnderUnderlyingChain, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- 概要：読み取った射列の最初の対象は c に等しい。
方針：左因子の固定条件を零番目の頂点で評価する。
規約：対象の等式を証明し逆構成で使用する。
使われ方：Under c の構造射の始域の固定。 -/
lemma nerveUnderUnderlyingChain_first {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) _⦋n⦌) :
    (nerveUnderUnderlyingChain c σ).obj 0 = c := by
  have hs := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ f)
    (nerveUnderUnderlyingChain_encode c σ)
  have he := hs.trans σ.property
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inl_vertex] at he
  have hh := congrArg (SSet.yonedaEquiv (X := nerve C)) he
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint] at hh
  exact congrArg (fun f : ComposableArrows C 0 ↦ f.obj 0) hh

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
