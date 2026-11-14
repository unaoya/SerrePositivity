module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedCompleteTop
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearPullback

/-! # 指定境界原始元を持つ実 pinched 辺

概要：零次元の二つの線形単体の差の原始元から、両端を持つ実辺を作る。
方針：二つの頂点と最上位の原始元を指定し、削除方程式の符号を直接計算する。
規約：微分は終点から始点を引く。使われ方：商内比較の実相対ホモトピーの基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 零次元の線形単体の唯一の成分。 -/
def pinchedLinearVertexValue (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0) : GradedHom A x y 0 :=
  s.val.component Finset.univ 0 Finset.univ_nonempty (by decide)

/-- 唯一の頂点成分は閉元。 -/
lemma pinchedLinearVertexValue_closed (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (pinchedLinearVertexValue s) = 0 :=
  (s.equation Finset.univ 0 Finset.univ_nonempty (by decide)).trans (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs])

/-- 両端と原始元を指定した一単体の成分族。 -/
def pinchedLinearBoundaryEdgeData (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0)
    (e : GradedHom A x y (-1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y 1 := fun i =>
  if hfull : i.val.1 = Finset.univ then by
    have hk : i.val.2 = -1 := by simpa [hfull] using i.property.2
    exact hk ▸ e
  else by
    have hc : i.val.1.card = 1 := by
      have hpos := i.property.1.card_pos
      have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hfull)
      have hle : i.val.1.card < 2 := by simpa using hlt
      omega
    have hk : i.val.2 = 0 := by simpa [hc] using i.property.2
    exact hk ▸ (if (0 : Fin 2) ∈ i.val.1 then pinchedLinearVertexValue s
      else pinchedLinearVertexValue t)

/-- 指定原始元の微分式により、二つの頂点を結ぶ線形単体が得られる。 -/
def pinchedLinearBoundaryEdge (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (-1))
    (he : (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d (-1) 0 e =
      pinchedLinearVertexValue t - pinchedLinearVertexValue s) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 1 :=
  ⟨pinchedLinearBoundaryEdgeData s t e, by
    intro J k hJ hk
    have hcases : J = ∅ ∨ J = {0} ∨ J = {1} ∨ J = Finset.univ := by
      fin_cases J <;> decide
    rcases hcases with rfl | rfl | rfl | rfl
    · simp at hJ
    · have hk0 : k = 0 := by simpa using hk
      subst hk0
      simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedLinearBoundaryEdgeData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs,
        pinchedLinearVertexValue] using pinchedLinearVertexValue_closed s
    · have hk0 : k = 0 := by simpa using hk
      subst hk0
      simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedLinearBoundaryEdgeData, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs,
        pinchedLinearVertexValue] using pinchedLinearVertexValue_closed t
    · have hk1 : k = -1 := by simpa using hk
      subst hk1
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rhs_eq_deleteSum]
      have hf : ({0, 1} : Finset (Fin 2)).filter (0 < ·) = {1} := by decide
      have hn : ({0, 1} : Finset (Fin 2)).Nontrivial := by decide
      have hsign : (2 : ℤ).negOnePow = 1 := by decide
      simpa [differential, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedLinearBoundaryEdgeData,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign, Finset.univ_fin2, pinchedLinearVertexValue, hf, hn, hsign,
        sub_eq_add_neg] using he⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
