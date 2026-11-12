module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplexDiagonalContractionNat
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：宇宙を合わせた反対単体圏の nerve は sifted である。
方針：二項対角の各 comma の明示的な弱収縮を Quillen 判定へ渡す。
規約：通常の圏の連結性だけへ弱めず、native な right cofinal 性を得る。
使われ方：P_Σ の幾何学的実現を既存の sifted 余極限から構成する。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 概要：通常の全右 comma の nerve の弱可縮性から元の nerve 写像は right cofinal。
方針：同じ native comma との同型で弱可縮性を移し Quillen 判定を使う。
規約：comma の始対象の存在は要求しない。
使われ方：反対単体圏の対角の高次 cofinal 性。 -/
lemma nerveMap_isRightCofinal_of_weaklyContractible_comma
    {P Q : Type u} [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (StructuredArrow q F))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro v
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective v
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso q F ≪≫ pullbackSymmetry _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mp (h q)

/-- 概要：元の反対単体圏の二項対角関手の nerve は right cofinal。
方針：各 comma の最小頂点の追加による弱収縮を用いる。
規約：元の持ち上げた単体次数を固定する。
使われ方：二項積への単体的な対角の比較。 -/
@[kerodon 02QP]
lemma simplexDegreeDiagonal_nerve_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDegreeDiagonal.{u}) :=
  nerveMap_isRightCofinal_of_weaklyContractible_comma _
    (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalComma_isWeaklyContractible q.1 q.2)

/-- 概要：宇宙を合わせた反対単体圏の nerve は sifted。
方針：非空性と、nerve の積比較を介した元の対角の cofinal 性を示す。
規約：元の小さい宇宙における sifted 性を与える。
使われ方：任意の小さい幾何学的実現への sifted 余極限定理の適用。 -/
@[kerodon 02QP]
instance smallSimplexOpposite_isSiftedInfinity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) where
  nonempty_vertices := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp (ULift.up (Opposite.op ⦋0⦌)))⟩
  diagonal_rightCofinal := by
    let q : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u} × _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) ⟶
        nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u} ⊗ nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u} :=
      prodComparison nerveFunctor (Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u})
        (Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u})
    have : IsIso q := inferInstance
    have h := simplexDegreeDiagonal_nerve_isRightCofinal.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso q)
    have he : nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDegreeDiagonal.{u} ≫ q =
        lift (𝟙 (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u})) (𝟙 _) := by
      dsimp only [q]
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc]
        erw [CartesianMonoidalCategory.prodComparison_fst]
        rw [lift_fst]
        rfl
      · rw [Category.assoc]
        erw [CartesianMonoidalCategory.prodComparison_snd]
        rw [lift_snd]
        rfl
    exact he ▸ h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
