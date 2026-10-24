module

public import SerrePositivity.InfinityCategories.F2.Presentable.SimplexDiagonalContractionNat
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedInfinity
public import SerrePositivity.InfinityCategories.F2.Presentable.NerveFinalInitialComma
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：宇宙を合わせた反対単体圏の nerve は sifted である。
方針：二項対角の各 comma の明示的な弱収縮を Quillen 判定へ渡す。
規約：通常の圏の連結性だけへ弱めず、native な right cofinal 性を得る。
使われ方：P_Σ の幾何学的実現を既存の sifted 余極限から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：通常の全右 comma の nerve の弱可縮性から元の nerve 写像は right cofinal。
方針：同じ native comma との同型で弱可縮性を移し Quillen 判定を使う。
規約：comma の始対象の存在は要求しない。
使われ方：反対単体圏の対角の高次 cofinal 性。 -/
lemma nerveMap_isRightCofinal_of_weaklyContractible_comma
    {P Q : Type u} [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, IsWeaklyContractible (nerve (StructuredArrow q F))) :
    IsRightCofinal (nerveMap F) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro v
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective v
  let e := F1B.nerveRightKanShapeIso q F ≪≫ pullbackSymmetry _ _
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mp (h q)

/-- 概要：元の反対単体圏の二項対角関手の nerve は right cofinal。
方針：各 comma の最小頂点の追加による弱収縮を用いる。
規約：元の持ち上げた単体次数を固定する。
使われ方：二項積への単体的な対角の比較。 -/
lemma simplexDegreeDiagonal_nerve_isRightCofinal :
    IsRightCofinal (nerveMap simplexDegreeDiagonal.{u}) :=
  nerveMap_isRightCofinal_of_weaklyContractible_comma _
    (fun q ↦ simplexDiagonalComma_isWeaklyContractible q.1 q.2)

/-- 概要：宇宙を合わせた反対単体圏の nerve は sifted。
方針：非空性と、nerve の積比較を介した元の対角の cofinal 性を示す。
規約：元の小さい宇宙における sifted 性を与える。
使われ方：任意の小さい幾何学的実現への sifted 余極限定理の適用。 -/
instance smallSimplexOpposite_isSiftedInfinity :
    HomotopyLimits.IsSiftedInfinity (nerve SmallSimplexOpposite.{u}) where
  nonempty_vertices := ⟨nerveVertex (ULiftHom.objUp (ULift.up (Opposite.op ⦋0⦌)))⟩
  diagonal_rightCofinal := by
    let q : nerve (SmallSimplexOpposite.{u} × SmallSimplexOpposite.{u}) ⟶
        nerve SmallSimplexOpposite.{u} ⊗ nerve SmallSimplexOpposite.{u} :=
      prodComparison nerveFunctor (Cat.of SmallSimplexOpposite.{u})
        (Cat.of SmallSimplexOpposite.{u})
    have : IsIso q := inferInstance
    have h := simplexDegreeDiagonal_nerve_isRightCofinal.comp (isRightCofinal_of_isIso q)
    have he : nerveMap simplexDegreeDiagonal.{u} ≫ q =
        lift (𝟙 (nerve SmallSimplexOpposite.{u})) (𝟙 _) := by
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

end SerrePositivity.InfinityCategories.F2.Presentable
