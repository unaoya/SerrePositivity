module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstUnitCollarGeometry
/-! # 終側の単位三角形による補正の再添字

概要：元終辺を保ちながら、元の三角形から終側の単位補正を貼った三角形へ移る。
方針：有限単調写像で終頂点だけを動かし、側面の単位貼り合わせを厳密に消去する。
規約：始辺・元端・全時間の終辺を明示的に回収する。
使われ方：後正規化の共有三角形を元 augmentation の固定 fiber 内で補正する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
def dgGluingLastUnitCollarPhase : Fin 3 × Fin 2 →o Fin 2 where
  toFun p := if p.1=2 then 1 else 0
  monotone' := by decide
def dgGluingLastUnitCollarVertex : Fin 3 × Fin 2 →o Fin 3 where
  toFun p := if p.1=2 then p.2.succ else p.1
  monotone' := by decide
def dgGluingLastUnitCollar : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[2] :=
  lift (stdSimplexProductMap dgGluingLastUnitCollarPhase)
    (stdSimplexProductMap dgGluingLastUnitCollarVertex)
lemma dgGluingLastUnitCollar_zero : (ι₀ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingLastUnitCollar =
    squareTriangle 0 ≫ (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingLastUnitCollar_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingLastUnitCollar =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ prismEndpoint 0 Δ[1] ≫
      (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 2 then 1 else 0) = 0
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    rw [hi]
    generalize h : p.1 j = q
    fin_cases q <;> rfl
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 2 then
      (p.2 j).succ else (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j)) =
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j)
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    simp only [hi]
    generalize h : p.1 j = q
    fin_cases q <;> rfl
def dgGluingLastUnitCollarSideOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := if p.1=0 then 0 else p.2
  monotone' := by decide
def dgGluingLastUnitCollarSide : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (stdSimplexProductMap dgGluingLastUnitCollarSideOrder)
lemma dgGluingLastUnitCollar_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingLastUnitCollar =
    dgGluingLastUnitCollarSide ≫ (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (p.1 j).succ = 2 then 1 else 0) = p.1 j
    generalize h : p.1 j = q
    fin_cases q <;> rfl
  · change (if (p.1 j).succ = 2 then (p.2 j).succ else (p.1 j).succ) =
      (if p.1 j=0 then 0 else p.2 j).succ
    generalize h : p.1 j = q
    fin_cases q <;> rfl
lemma dgGluingLastUnitCollarSide_zero :
    squareTriangle (0 : Fin 2) ≫ dgGluingLastUnitCollarSide.{u} =
    stdSimplex.σ (0 : Fin 2) ≫ squareDiagonal := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingLastUnitCollarSide_one :
    squareTriangle (1 : Fin 2) ≫ dgGluingLastUnitCollarSide.{u} = squareTriangle 1 := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingSquareUnitCollapse_last_diagonal :
    squareDiagonal ≫ dgGluingSquareUnitCollapse.{u} 1 = 𝟙 Δ[1] := by
  rw [← squareTriangle_diagonal 0, Category.assoc, dgGluingSquareUnitCollapse_triangle]
  apply SSet.yonedaEquiv.injective
  decide
lemma dgGluingLastUnitCollarSide_collapse :
    dgGluingLastUnitCollarSide.{u} ≫ dgGluingSquareUnitCollapse 1 =
    fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply square_isPushout.hom_ext
  · rw [← Category.assoc, dgGluingLastUnitCollarSide_zero, Category.assoc,
      dgGluingSquareUnitCollapse_last_diagonal,
      Category.comp_id]
    apply SSet.yonedaEquiv.injective
    decide
  · rw [← Category.assoc, dgGluingLastUnitCollarSide_one, dgGluingSquareUnitCollapse_triangle]
    apply SSet.yonedaEquiv.injective
    decide
end SerrePositivity.InfinityCategories
