module
public import SerrePositivity.KST.Fibration.WeakStringCofiberFamilies
public import SerrePositivity.KST.Fibration.CofiberFamilyComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronSquares

/-! # W 列の全二単体の八面体の族

W 列図式圏全体をパラメーターとする関手圏で実八面体を構成する。
長辺・第二短辺の補完を、既存の共通補完と図式全体の自然同型で比較する。
異なる再添字に対する八面体の選択の比較と列全体の加法性は別工程である。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の全二単体の第一短辺は、共通 cofiber 族の元の底辺である。 -/
lemma weakStringCofiberFamily_triangle_bottom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (weakStringCofiberFamily q (SimplexCategory.δ (2 : Fin 3) ≫ β)).square =
      stdSimplex.δ (2 : Fin 3) ≫ (stdSimplex.map β ≫ weakStringUniversalFamily q n) := by
  rw [weakStringCofiberFamily_bottom, Functor.map_comp, Category.assoc]
  rfl

/-- 全高次自然変換を保持した、指定二単体の実八面体の族。 -/
def weakStringOctahedronFamily {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram
      (weakStringCofiberFamily q (SimplexCategory.δ (2 : Fin 3) ≫ β))
      (stdSimplex.map β ≫ weakStringUniversalFamily q n) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberOctahedronDiagram _
    (weakStringCofiberFamily_isCofiber q _) _ (weakStringCofiberFamily_triangle_bottom q β))

/-- 八面体の長辺の補完と既存の共通補完は、全図式として自然同型である。 -/
def weakStringOctahedronFamily_compositeComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringOctahedronFamily q β).first.outerZeroTriangle.square
      (weakStringCofiberFamily q (SimplexCategory.δ (1 : Fin 3) ≫ β)).square := by
  let d := weakStringOctahedronFamily q β
  apply cofiberFamilyComparison d.first.outerZeroTriangle _ d.first.outer_isCofiber
    (weakStringCofiberFamily_isCofiber q _)
  have hb := d.compositeCofiberSquare.bottom_edge
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.first.outerZeroTriangle.square =
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      (stdSimplex.δ (1 : Fin 3) ≫ (stdSimplex.map β ≫ weakStringUniversalFamily q n))) at hb
  rw [SSet.yonedaEquiv.symm_apply_apply] at hb
  rw [weakStringCofiberFamily_bottom, Functor.map_comp, Category.assoc]
  exact hb

/-- 八面体の第二短辺の補完も、全パラメーターを保って既存の共通補完と比較する。 -/
def weakStringOctahedronFamily_nextComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringOctahedronFamily q β).second.outerZeroTriangle.square
      (weakStringCofiberFamily q (SimplexCategory.δ (0 : Fin 3) ≫ β)).square := by
  let d := weakStringOctahedronFamily q β
  apply cofiberFamilyComparison d.second.outerZeroTriangle _ d.second.outer_isCofiber
    (weakStringCofiberFamily_isCofiber q _)
  have hb := d.nextCofiberSquare.bottom_edge
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.second.outerZeroTriangle.square =
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 3) ≫ (stdSimplex.map β ≫ weakStringUniversalFamily q n))) at hb
  rw [SSet.yonedaEquiv.symm_apply_apply] at hb
  rw [weakStringCofiberFamily_bottom, Functor.map_comp, Category.assoc]
  exact hb

end SerrePositivity.KST.Fibration
