module

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

def postIndex : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then 0 else if p.2 = 0 then 1 else 2
  monotone' := by decide

def preIndex : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 1 then 2 else p.2.castSucc
  monotone' := by decide

def factorIndex : Fin 2 × Fin 3 →o Fin 2 where
  toFun p := if p.2 = 0 then 0 else if p.2 = 1 then p.1 else 1
  monotone' := by decide

def postShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] := gridMap postIndex

def preShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] := gridMap preIndex

def factor : (Δ[1] : SSet.{u}) ⊗ Δ[2] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (gridMap factorIndex)

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
    change factorIndex (s i, (1 : Fin 3).succAbove (t i)) = t i
    generalize ht : t i = b
    fin_cases b <;> rfl

lemma factor_first : (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) ≫ factor.{u} =
    postShape ≫ squareTriangle 1 := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i
  · change s i = (squareTriangleSimplex.{u} (1 : Fin 2)).val.1 (postIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl
  · change factorIndex (s i, (2 : Fin 3).succAbove (t i)) =
      (squareTriangleSimplex.{u} (1 : Fin 2)).val.2 (postIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl

lemma factor_last : (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) ≫ factor.{u} =
    preShape ≫ squareTriangle 0 := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i
  · change s i = (squareTriangleSimplex.{u} (0 : Fin 2)).val.1 (preIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl
  · change factorIndex (s i, (t i).succ) =
      (squareTriangleSimplex.{u} (0 : Fin 2)).val.2 (preIndex (s i, t i))
    generalize hs : s i = a
    generalize ht : t i = b
    fin_cases a <;> fin_cases b <;> rfl

end SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
