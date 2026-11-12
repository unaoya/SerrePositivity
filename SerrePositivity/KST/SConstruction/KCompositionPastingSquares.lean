module
public import SerrePositivity.KST.SConstruction.ThreeSquarePasting
public import SerrePositivity.KST.SConstruction.KCompositionPrismExteriorConstants

/-! # 元の K 合成 prism の三正方形の貼り合わせ
概要：共有区間を保った同じ三正方形を、一つの元の suspension Hom への写像にする。
方針：元の prism の共有面の厳密な等号を二つの pushout に渡す。
規約：元の三正方形全体と外側二定数辺を保持する。
使われ方：指定適合三角形を同じ境界に付けるための実入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPastingSquaresPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三正方形を貼った、元の suspension Hom への実写像。 -/
def kKanOriginalCompositionPastingSquares : threeSquarePasting ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  threeSquarePastingMap
    (kKanOriginalCompositionMappingSquare r F f g 0)
    (kKanOriginalCompositionMappingSquare r F f g 1)
    (kKanOriginalCompositionMappingSquare r F f g 2)
    (kKanOriginalCompositionMappingSquare_shared_first r F f g)
    (kKanOriginalCompositionMappingSquare_shared_second r F f g)

/-- 元の各正方形全体を、同じ Hom 内で厳密に回収する。 -/
lemma kKanOriginalCompositionPastingSquares_square (q : Fin 3) :
    threeSquareInclusion q ≫ kKanOriginalCompositionPastingSquares r F f g =
      kKanOriginalCompositionMappingSquare r F f g q := by
  have h := threeSquarePastingMap_inclusion
    (kKanOriginalCompositionMappingSquare r F f g 0)
    (kKanOriginalCompositionMappingSquare r F f g 1)
    (kKanOriginalCompositionMappingSquare r F f g 2)
    (kKanOriginalCompositionMappingSquare_shared_first r F f g)
    (kKanOriginalCompositionMappingSquare_shared_second r F f g) q
  change threeSquareInclusion q ≫ kKanOriginalCompositionPastingSquares r F f g = _ at h
  exact h.trans (by fin_cases q <;> rfl)

/-- 最初の外側辺の元の定数性を、貼り合わせ後も同じ区間で保持する。 -/
lemma kKanOriginalCompositionPastingSquares_exterior_upper_constant :
    ∃ v, pastingSquareVertical 1 ≫ threeSquareInclusion 0 ≫
      kKanOriginalCompositionPastingSquares r F f g = SSet.const v := by
  rw [kKanOriginalCompositionPastingSquares_square]
  exact kKanOriginalCompositionMappingSquare_exterior_upper_constant r F f g

/-- 最後の外側辺の元の定数性も、貼り合わせ後の同じ区間で保持する。 -/
lemma kKanOriginalCompositionPastingSquares_exterior_lower_constant :
    ∃ v, pastingSquareHorizontal 1 ≫ threeSquareInclusion 2 ≫
      kKanOriginalCompositionPastingSquares r F f g = SSet.const v := by
  rw [kKanOriginalCompositionPastingSquares_square]
  exact kKanOriginalCompositionMappingSquare_exterior_lower_constant r F f g

end SerrePositivity.KST.SConstruction
