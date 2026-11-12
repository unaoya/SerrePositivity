module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralIndices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedHomReplacement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-! # 任意次元の最後外ホーンの欠面残差と未知 Q

概要：次元 n+2 の欠面から閉じた残差を回収し、次数 −n の Q の挿入と全真部分方程式を検証。
方針：一般欠面の端点・濃度と Bianchi、指定成分の置換を使う。
規約：n=0 も含む。使われ方：高次有限図式の二未知充填と残差 cone への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 任意次元の実最後ホーンの欠面の、次数 −n+1 の微分右辺。 -/
def dgGeneralLastHornMissingResidual :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ) + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n)

/-- 回収既知データの欠面未知成分は、全次元で零。 -/
lemma dgGeneralLastHornMissingHom_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)
      (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) = 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData]
  split_ifs with hf hm
  · exact (hm rfl).elim
  · rfl
  · rfl

/-- 欠面の実右辺は、ホーンの既知方程式から閉じている。 -/
lemma dgGeneralLastHornMissingResidual_closed :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgGeneralLastHornMissingResidual σ) = 0 := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ
  have hp : ∀ J ⊂ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n), s.Equation J := by
    intro J hJ
    have hf : J ≠ Finset.univ := by
      intro he
      have hl : Fin.last (n + 2) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n :=
        hJ.1 (he.symm ▸ Finset.mem_univ _)
      exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hl
    have hm : J ≠ Finset.univ.erase (Fin.last (n + 2)) :=
      (Finset.ssubset_iff_subset_ne.mp hJ).2
    intro a b k hI ha hb hk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ J a b k hI ha hb hk hf hm
  exact s.differential_rhs_zero_of_proper_equations (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) hp
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n)

variable (Q : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ)))

/-- 欠面の最上位成分のみを Q で置き換えた実データ。 -/
def dgGeneralLastHornQData : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).replaceFixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q

/-- Q の挿入は、任意次元の実最後ホーンの全指定面を全て厳密に保つ。 -/
lemma dgGeneralLastHornQData_face (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
    (dgGeneralLastHornQData σ Q).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (horn.face (Fin.last (n + 2)) j hj)).toSimplexData := by
  have hm : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_mem j).mpr hj
  unfold dgGeneralLastHornQData _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j hm (Fin.succAbove_ne j)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj

/-- Q の実微分式が成り立てば、欠面の方程式が成立する。 -/
lemma dgGeneralLastHornQData_missingEquation
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgGeneralLastHornMissingResidual σ) :
    (dgGeneralLastHornQData σ Q).Equation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
    0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n)
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_same (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (-(n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_two n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_min n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex_degree n) Q
  exact (congrArg (fun f => differential A f) hl).trans (dQ.trans hr.symm)

/-- Q の微分式が成り立てば、最上位以外の実データの全方程式が成立する。 -/
lemma dgGeneralLastHornQData_properEquations
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgGeneralLastHornMissingResidual σ)
    (I : Finset (Fin (n + 3))) (hf : I ≠ Finset.univ) :
    (dgGeneralLastHornQData σ Q).Equation I := by
  by_cases hm : I = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex n)
  · subst I
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_missingEquation σ Q dQ
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.equation_of_faces σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_face σ Q) I hf
    exact hm

/-- Q の実微分式を解いた後の最上位右辺は閉じている。 -/
lemma dgGeneralLastHornQData_topRhs_closed
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgGeneralLastHornMissingResidual σ) :
    _root_.SerrePositivity.DifferentialGraded.differential A ((dgGeneralLastHornQData σ Q).rhs Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n)) = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_rhs_zero_of_proper_equations
  intro J hJ
  exact dgGeneralLastHornQData_properEquations σ Q dQ J
    (Finset.ssubset_iff_subset_ne.mp hJ).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
