module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralIndices
public import SerrePositivity.InfinityCategories.DGNerve.FixedHomReplacement
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation
public import SerrePositivity.InfinityCategories.DGNerve.ProperEquationBianchi
public import SerrePositivity.InfinityCategories.DGNerve.EquationTransfer

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 任意次元の実最後ホーンの欠面の、次数 −n+1 の微分右辺。 -/
def dgGeneralLastHornMissingResidual :
    GradedHom A ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (dgLastHornPenultimate n)) (-(n : ℤ) + 1) :=
  (HornData.knownData σ).rhs (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)

/-- 回収既知データの欠面未知成分は、全次元で零。 -/
lemma dgGeneralLastHornMissingHom_zero :
    (HornData.knownData σ).hom (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n)
      (-(n : ℤ)) (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n) = 0 := by
  dsimp only [HornData.knownData]
  split_ifs with hf hm
  · exact (hm rfl).elim
  · rfl
  · rfl

/-- 欠面の実右辺は、ホーンの既知方程式から閉じている。 -/
lemma dgGeneralLastHornMissingResidual_closed :
    differential A (dgGeneralLastHornMissingResidual σ) = 0 := by
  let s := HornData.knownData σ
  have hp : ∀ J ⊂ (dgLastHornMissingIndex n), s.Equation J := by
    intro J hJ
    have hf : J ≠ Finset.univ := by
      intro he
      have hl : Fin.last (n + 2) ∈ dgLastHornMissingIndex n :=
        hJ.1 (he.symm ▸ Finset.mem_univ _)
      exact (Finset.notMem_erase (Fin.last (n + 2)) Finset.univ) hl
    have hm : J ≠ Finset.univ.erase (Fin.last (n + 2)) :=
      (Finset.ssubset_iff_subset_ne.mp hJ).2
    intro a b k hI ha hb hk
    exact HornData.knownData_equation σ J a b k hI ha hb hk hf hm
  exact s.differential_rhs_zero_of_proper_equations (dgLastHornMissingIndex n) hp
    0 (dgLastHornPenultimate n) (-(n : ℤ)) (dgLastHornMissingIndex_two n)
      (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)

variable (Q : GradedHom A ((HornData.knownData σ).obj 0)
  ((HornData.knownData σ).obj (dgLastHornPenultimate n)) (-(n : ℤ)))

/-- 欠面の最上位成分のみを Q で置き換えた実データ。 -/
def dgGeneralLastHornQData : SimplexData A D (n + 2) :=
  (HornData.knownData σ).replaceFixed (dgLastHornMissingIndex n)
    0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n) Q

/-- Q の挿入は、任意次元の実最後ホーンの全指定面を全て厳密に保つ。 -/
lemma dgGeneralLastHornQData_face (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
    (dgGeneralLastHornQData σ Q).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (horn.face (Fin.last (n + 2)) j hj)).toSimplexData := by
  have hm : j ∈ dgLastHornMissingIndex n := (dgLastHornMissingIndex_mem j).mpr hj
  unfold dgGeneralLastHornQData SimplexData.replaceFixed
  rw [SimplexData.replace_pullback_of_omits _ _ _ _ j hm (Fin.succAbove_ne j)]
  exact HornData.knownData_pullback_face σ j hj

/-- Q の実微分式が成り立てば、欠面の方程式が成立する。 -/
lemma dgGeneralLastHornQData_missingEquation
    (dQ : differential A Q = dgGeneralLastHornMissingResidual σ) :
    (dgGeneralLastHornQData σ Q).Equation (dgLastHornMissingIndex n) := by
  apply SimplexData.equation_of_fixed _ (dgLastHornMissingIndex n)
    0 (dgLastHornPenultimate n) (-(n : ℤ))
    (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n)
  have hl := SimplexData.replaceFixed_hom_same (HornData.knownData σ)
    (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
      (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n) Q
  have hr := SimplexData.replaceFixed_rhs_self (HornData.knownData σ)
    (dgLastHornMissingIndex n) 0 (dgLastHornPenultimate n) (-(n : ℤ))
      (dgLastHornMissingIndex_two n) (dgLastHornMissingIndex_min n)
      (dgLastHornMissingIndex_max n) (dgLastHornMissingIndex_degree n) Q
  exact (congrArg (fun f => differential A f) hl).trans (dQ.trans hr.symm)

/-- Q の微分式が成り立てば、最上位以外の実データの全方程式が成立する。 -/
lemma dgGeneralLastHornQData_properEquations
    (dQ : differential A Q = dgGeneralLastHornMissingResidual σ)
    (I : Finset (Fin (n + 3))) (hf : I ≠ Finset.univ) :
    (dgGeneralLastHornQData σ Q).Equation I := by
  by_cases hm : I = (dgLastHornMissingIndex n)
  · subst I
    exact dgGeneralLastHornQData_missingEquation σ Q dQ
  · apply HornData.equation_of_faces σ _ (dgGeneralLastHornQData_face σ Q) I hf
    exact hm

/-- Q の実微分式を解いた後の最上位右辺は閉じている。 -/
lemma dgGeneralLastHornQData_topRhs_closed
    (dQ : differential A Q = dgGeneralLastHornMissingResidual σ) :
    differential A ((dgGeneralLastHornQData σ Q).rhs Finset.univ 0 (Fin.last (n + 2)) (-(n : ℤ) - 1)
      (dgLastHornTop_two n)
      (dgLastHornTop_min n) (dgLastHornTop_max n) (dgLastHornTop_degree n)) = 0 := by
  apply SimplexData.differential_rhs_zero_of_proper_equations
  intro J hJ
  exact dgGeneralLastHornQData_properEquations σ Q dQ J
    (Finset.ssubset_iff_subset_ne.mp hJ).2

end SerrePositivity.InfinityCategories
