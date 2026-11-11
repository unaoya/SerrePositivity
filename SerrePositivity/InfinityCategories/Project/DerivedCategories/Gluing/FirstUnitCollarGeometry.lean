module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationAugmentationUnitSquares
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap

/-! # 始側の単位三角形による補正の再添字

概要：元の三角形と単位側面を貼った三角形を、同じ固定始辺を持つ区間族でつなぐ。
方針：頂点と時間の有限単調写像を使い、側面の単位貼り合わせを厳密に消去する。
規約：再添字と全境界を明示し、ホモトピーの存在だけでは置き換えない。
使われ方：標準正規化の前側を元 augmentation の固定 fiber へ戻す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
def dgGluingFirstUnitCollarPhase : Fin 3 × Fin 2 →o Fin 2 where
  toFun p := if p.1=0 then 0 else 1
  monotone' := by decide
def dgGluingFirstUnitCollarVertex : Fin 3 × Fin 2 →o Fin 3 where
  toFun p := if p.1=0 then p.2.castSucc else p.1
  monotone' := by decide
def dgGluingFirstUnitCollar : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[2] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingFirstUnitCollarPhase)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingFirstUnitCollarVertex)
lemma dgGluingFirstUnitCollar_one : (ι₁ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingFirstUnitCollar =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingFirstUnitCollar_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingFirstUnitCollar =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫
      (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals rfl


def dgGluingFirstUnitCollarSideOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := max p.1 p.2
  monotone' {_a _b} h := max_le_max h.1 h.2
def dgGluingFirstUnitCollarSide : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingFirstUnitCollarSideOrder)
lemma dgGluingFirstUnitCollar_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingFirstUnitCollar =
    dgGluingFirstUnitCollarSide ≫ (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 0 then 0 else 1) = p.1 j
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    rw [hi]
    generalize h : p.1 j = q
    fin_cases q <;> rfl
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 0 then
      (p.2 j).castSucc else (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j)) =
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom (max (p.1 j) (p.2 j))
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    simp only [hi]
    generalize h : p.1 j = q
    generalize h' : p.2 j = t
    fin_cases q <;> fin_cases t <;> rfl

lemma dgGluingFirstUnitCollarSide_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2) ≫ dgGluingFirstUnitCollarSide.{u} =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingFirstUnitCollarSide_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (1 : Fin 2) ≫ dgGluingFirstUnitCollarSide.{u} =
    stdSimplex.σ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingSquareUnitCollapse_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareDiagonal ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse.{u} 0 = 𝟙 Δ[1] := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal 0, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse_triangle]
  apply SSet.yonedaEquiv.injective
  decide
lemma dgGluingFirstUnitCollarSide_collapse :
    dgGluingFirstUnitCollarSide.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0 =
    fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← Category.assoc, dgGluingFirstUnitCollarSide_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse_triangle]
    apply SSet.yonedaEquiv.injective
    decide
  · rw [← Category.assoc, dgGluingFirstUnitCollarSide_one, Category.assoc,
      dgGluingSquareUnitCollapse_diagonal,
      Category.comp_id]
    apply SSet.yonedaEquiv.injective
    decide
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
