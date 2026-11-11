module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedHomReplacement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-! # 実四次最後外ホーンの欠面残差と未知 Q

概要：実四次ホーンの欠けた三次面の閉残差を回収し、次数 −2 の Q の挿入を接続する。
方針：真部分集合の既知方程式と Bianchi、固定成分の置換を使う。
規約：符号は実 rhs に従う。使われ方：四次整合性の二未知 cochain と残差 cone の構成。
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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実四次ホーンの欠けた三次面の、次数 −1 の微分右辺。 -/
def dgFourLastHornMissingResidual :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2 + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).rhs {0, 1, 2, 3} 0 3 (-2)
    (by decide) (by decide) (by decide) (by decide)

/-- 欠面の実右辺は、ホーンの既知方程式から閉じている。 -/
lemma dgFourLastHornMissingResidual_closed :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgFourLastHornMissingResidual σ) = 0 := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ
  have hp : ∀ J ⊂ ({0, 1, 2, 3} : Finset (Fin 5)), s.Equation J := by
    intro J hJ
    have hf : J ≠ Finset.univ := by
      intro he
      have h₄ : (4 : Fin 5) ∈ J := he.symm ▸ Finset.mem_univ 4
      exact (by decide : (4 : Fin 5) ∉ ({0, 1, 2, 3} : Finset (Fin 5))) (hJ.1 h₄)
    have hm : J ≠ Finset.univ.erase (4 : Fin 5) := by
      intro he
      exact (Finset.ssubset_iff_subset_ne.mp hJ).2 (he.trans (by decide))
    intro a b k hI ha hb hk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ J a b k hI ha hb hk hf hm
  exact s.differential_rhs_zero_of_proper_equations {0, 1, 2, 3} hp
    0 3 (-2) (by decide) (by decide) (by decide) (by decide)

variable (Q : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2))

/-- 欠けた三次面の最上位成分のみを Q で置き換えた実データ。 -/
def dgFourLastHornQData : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D 4 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).replaceFixed {0, 1, 2, 3} 0 3 (-2)
    (by decide) (by decide) (by decide) (by decide) Q

/-- Q の挿入は、実四次ホーンの指定四面を全て厳密に保つ。 -/
lemma dgFourLastHornQData_face (j : Fin 5) (hj : j ≠ 4) :
    (dgFourLastHornQData σ Q).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (horn.face 4 j hj)).toSimplexData := by
  have hm : j ∈ ({0, 1, 2, 3} : Finset (Fin 5)) := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 5)) = Finset.univ.erase 4 from by decide]
    exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  unfold dgFourLastHornQData _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j hm (Fin.succAbove_ne j)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj

/-- Q の実微分式が成り立てば、欠けた三次面の方程式が成立する。 -/
lemma dgFourLastHornQData_missingEquation
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgFourLastHornMissingResidual σ) :
    (dgFourLastHornQData σ Q).Equation {0, 1, 2, 3} := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed _ {0, 1, 2, 3} 0 3 (-2)
    (by decide) (by decide) (by decide) (by decide)
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_same (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) Q
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    {0, 1, 2, 3} 0 3 (-2) (by decide) (by decide) (by decide) (by decide) Q
  exact (congrArg (fun f => differential A f) hl).trans (dQ.trans hr.symm)

/-- Q の微分式が成り立てば、最上位以外の実四次データの全方程式が成立する。 -/
lemma dgFourLastHornQData_properEquations
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgFourLastHornMissingResidual σ)
    (I : Finset (Fin 5)) (hf : I ≠ Finset.univ) : (dgFourLastHornQData σ Q).Equation I := by
  by_cases hm : I = {0, 1, 2, 3}
  · subst I
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornQData_missingEquation σ Q dQ
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.equation_of_faces σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornQData_face σ Q) I hf
    simpa only [show (Finset.univ : Finset (Fin 5)).erase 4 = {0, 1, 2, 3} from by decide] using hm

/-- Q の実微分式を解いた後の最上位右辺は閉じている。 -/
lemma dgFourLastHornQData_topRhs_closed
    (dQ : _root_.SerrePositivity.DifferentialGraded.differential A Q = dgFourLastHornMissingResidual σ) :
    _root_.SerrePositivity.DifferentialGraded.differential A ((dgFourLastHornQData σ Q).rhs Finset.univ 0 4 (-3)
      (by decide) (by decide) (by decide) (by decide)) = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_rhs_zero_of_proper_equations
  intro J hJ
  exact dgFourLastHornQData_properEquations σ Q dQ J
    (Finset.ssubset_iff_subset_ne.mp hJ).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
