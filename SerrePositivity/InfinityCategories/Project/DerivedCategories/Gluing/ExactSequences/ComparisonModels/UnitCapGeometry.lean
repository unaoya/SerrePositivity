module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.LastUnitCollarFamilies
/-! # 単位補正端から標準合成三角形への再添字

概要：補正済み角の三角形を、同じ始辺または終辺を保って射影側の標準合成面へつなぐ。
方針：一つの augmentation 時刻だけを動かし、単位側面の対称性で固定辺を回収する。
規約：両単位補正端と標準射影面を厳密に保持する。
使われ方：実前正規化と実終側合成から、正本の二つの標準合成三角形へ移る。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingSquareTriangle_swap (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i.rev := by
  fin_cases i <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro j <;> fin_cases j <;> rfl
lemma dgGluingSquareUnitCollapse_swap (i : Fin 2) :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  all_goals rw [← Category.assoc, dgGluingSquareTriangle_swap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse_triangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse_triangle]
def dgGluingFirstUnitCapPhase : Fin 3 × Fin 2 →o Fin 2 where
  toFun p := if p.1=0 then p.2 else 1
  monotone' := by decide
def dgGluingFirstUnitCap : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[2] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingFirstUnitCapPhase) (fst _ _)
lemma dgGluingFirstUnitCap_zero : (ι₀ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingFirstUnitCap =
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollar := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingFirstUnitCap_one : (ι₁ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingFirstUnitCap =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[2] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingFirstUnitCap_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingFirstUnitCap =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom) ≫
        (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 0 then
      p.2 j else 1) = max (p.1 j) (p.2 j)
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    rw [hi]
    generalize h : p.1 j = q
    generalize h' : p.2 j = t
    fin_cases q <;> fin_cases t <;> rfl
  · rfl
lemma dgGluingFirstUnitCap_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingFirstUnitCap =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫
        (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; rfl

def dgGluingLastUnitCapPhase : Fin 3 × Fin 2 →o Fin 2 where
  toFun p := if p.1=2 then p.2 else 0
  monotone' := by decide
def dgGluingLastUnitCap : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[2] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap dgGluingLastUnitCapPhase) (fst _ _)
lemma dgGluingLastUnitCap_zero : (ι₀ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingLastUnitCap =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[2] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingLastUnitCap_one : (ι₁ : (Δ[2] : SSet.{u}) ⟶ _) ≫ dgGluingLastUnitCap =
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollar := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j; fin_cases j <;> rfl
lemma dgGluingLastUnitCap_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingLastUnitCap =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom) ≫
        (Δ[1] ◁ stdSimplex.δ (0 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (p.1 j).succ = 2 then p.2 j else 0) =
      (if p.1 j=0 then 0 else p.2 j)
    generalize h : p.1 j = q
    fin_cases q <;> rfl
  · rfl
lemma dgGluingLastUnitCap_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ dgGluingLastUnitCap =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫
        (Δ[1] ◁ stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  · change (if (SimplexCategory.δ (2 : Fin 3)).toOrderHom (p.1 j) = 2 then p.2 j else 0) = 0
    have hi (q : Fin 2) : (SimplexCategory.δ (2 : Fin 3)).toOrderHom q = q.castSucc := by
      fin_cases q <;> rfl
    rw [hi]
    generalize h : p.1 j = q
    fin_cases q <;> rfl
  · rfl
lemma dgGluingFirstUnitCapSide_collapse :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 0 = fst (Δ[1] : SSet.{u}) Δ[1] := by
  rw [Category.assoc, dgGluingSquareUnitCollapse_swap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstUnitCollarSide_collapse]
lemma dgGluingLastUnitCapSide_collapse :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareUnitCollapse 1 = fst (Δ[1] : SSet.{u}) Δ[1] := by
  rw [Category.assoc, dgGluingSquareUnitCollapse_swap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastUnitCollarSide_collapse]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
