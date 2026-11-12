module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareDiagonalShape

public import SerrePositivity.KST.LocalizingInvariants.GridSimplexMap

/-!
概要：元の正方形を下辺・共通対角・上辺の合成三角形で分解する形状写像。
方針：有限格子の単調写像で、二つの三角形への退化写像と全合成族を構成する。
規約：正方形の向きは第一因子が辺、第二因子が比較。使われ方：全 h Fun の右辺分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareDiagonal

def postShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] := gridMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.postIndex

def preShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] := gridMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex

def factor : (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (gridMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.factorIndex)

lemma postShape_zero : SSet.ι₀ ≫ postShape.{u} = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma postShape_one : SSet.ι₁ ≫ postShape.{u} = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma preShape_zero : SSet.ι₀ ≫ preShape.{u} = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma preShape_one : SSet.ι₁ ≫ preShape.{u} = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma factor_long : (Δ[1] ◁ stdSimplex.δ (1 : Fin 3)) ≫ factor.{u} = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro i
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.factorIndex (s i, (1 : Fin 3).succAbove (t i)) = t i
    generalize ht : t i = b
    fin_cases b <;> rfl

lemma factor_first : (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ factor.{u} =
    postShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i
  · change s i = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} (1 : Fin 2)).val.1 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.postIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl
  · change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.factorIndex (s i, (2 : Fin 3).succAbove (t i)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} (1 : Fin 2)).val.2 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.postIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl

lemma factor_last : (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ factor.{u} =
    preShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i
  · change s i = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} (0 : Fin 2)).val.1 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl
  · change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.factorIndex (s i, (t i).succ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangleSimplex.{u} (0 : Fin 2)).val.2 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.preIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl

end SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
