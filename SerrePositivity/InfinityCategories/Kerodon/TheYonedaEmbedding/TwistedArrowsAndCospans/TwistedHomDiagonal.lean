module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomRows
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction

/-!
概要：各行の coslice 比較を二重単体自然変換に束ね、対角で元の主比較を回収する。
方針：形の崩壊の一意性で左の添字の自然性を示し、左右の制限を同時に作用させる。
規約：対角の射は元の cosliceTwistedHomMap そのものであることを厳密に照合する。
使われ方：各行の同値性を主比較の同値性へ移す。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 各行への拡張は左の全ての面・退化に対して自然。 -/
lemma twistedHomRowAugment_naturality {C : SSet.{u}} (x y : C _⦋0⦌)
    {m n : SimplexCategory} (α : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment x y n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowMap x y α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment x y m := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map α)) (𝟙 _) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse n) (𝟙 _) ≫ F.val.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse m) (𝟙 _) ≫ F.val.val
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  have h : SSet.opFunctor.map (stdSimplex.map α) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse m := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]

/-- 元の coslice fiber から各行への一つの二重単体自然変換。 -/
def twistedHomRowsAugmentation {C : SSet.{u}} (x y : C _⦋0⦌) :
    (Functor.const SimplexCategoryᵒᵖ).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRows x y where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment x y n.unop
  naturality {m n} α := by
    change 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment x y n.unop =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment x y m.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowMap x y α.unop
    rw [Category.id_comp]
    exact (twistedHomRowAugment_naturality x y α.unop).symm

/-- 定値な二重単体図式の対角は、元の単体集合と厳密に同型。 -/
def diagonalConstantIso (K : SSet.{u}) :
    SerrePositivity.BisimplicialModel.diagonal.obj ((Functor.const SimplexCategoryᵒᵖ).obj K) ≅ K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

/-- 左右の添字が一致する対角は、元の twisted arrow の両端固定の写像空間そのもの。 -/
def twistedHomDiagonalIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    SerrePositivity.BisimplicialModel.diagonal.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRows x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace x y :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun := fun F ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpaceSimplex x y F.val F.property.1 F.property.2
      invFun := fun F ↦ ⟨F.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace_left F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace_right F⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl }) (by
        intro n m α
        apply ConcreteCategory.hom_ext
        intro F
        apply Subtype.ext
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (stdSimplex.map α.unop) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map α.unop)) (𝟙 _) ≫ F.val) =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map α.unop)) (stdSimplex.map α.unop) ≫ F.val
        simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id])

/-- 対角の比較を両側の厳密な表示同型で戻すと、元の主比較射を回収する。 -/
lemma cosliceTwistedHomMap_eq_diagonal {C : SSet.{u}} (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap x y =
      (diagonalConstantIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)).inv ≫
        SerrePositivity.BisimplicialModel.diagonal.map (twistedHomRowsAugmentation x y) ≫
          (twistedHomDiagonalIso x y).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgewiseCollapse ⦋n⦌ ≫ F.val.val =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse ⦋n⦌) (𝟙 _) ≫ F.val.val
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceSimplexCollapse.{u} ⦋n⦌ =
      SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
