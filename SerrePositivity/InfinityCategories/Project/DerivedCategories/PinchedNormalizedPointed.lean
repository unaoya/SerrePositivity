module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedNormalizedFillerFaces
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct

/-! # 指定原始元による正規化された差の実零ホモトピー関係

概要：正規化された差を実 pointed simplex とし、一段高い充填から RelStruct₀ を作る。
方針：零線形単体と定値写像を同定し、全ての実面の厳密一致を使う。
規約：元の二単体の prism homotopy は別途必要。使われ方：正次元比較の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 零線形単体の逆構成は、任意の引き戻しで零線形単体へ移る。 -/
lemma pinchedZeroSimplex_pullback {m n : SimplexCategory} (α : m ⟶ n) :
    (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n.len).toPinched.pullback α =
      (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y m.len).toPinched := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y m.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n.len).toPinched.pullback α) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y m.len).toPinched
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, map_zero]

/-- 全ての零線形単体は、実際の同じ零頂点の定値単体。 -/
lemma pinchedZeroSimplex_constant (n : ℕ) :
    SSet.yonedaEquiv.symm (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n).toPinched =
      SSet.const (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched := by
  let α := SimplexCategory.const ⦋n⦌ ⦋0⦌ 0
  have hz := pinchedZeroSimplex_pullback (A := A) (x := x) (y := y) α
  calc
    _ = SSet.stdSimplex.map α ≫ SSet.yonedaEquiv.symm
        (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched := by
      rw [SSet.yonedaEquiv_symm_naturality_left]
      exact congrArg SSet.yonedaEquiv.symm hz.symm
    _ = _ := by rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 正規化された線形単体は、実零頂点を基点とする pointed simplex。 -/
def pinchedNormalizedPointed {n : ℕ} (z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y).PtSimplex (n + 1)
      (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched where
  map := SSet.yonedaEquiv.symm z.toPinched
  comm := by
    change (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm z.toPinched =
      SSet.const (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched
    apply SSet.boundary.hom_ext
    intro j
    rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      SSet.comp_const, ← pinchedZeroSimplex_constant n]
    exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedNormalizedSimplex_face_zero z hz j)

/-- 指定原始元から、差と定値零の間の実 pointed simplex の零ホモトピー関係を得る。 -/
def PinchedTopComparison.normalizedRelStruct {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.PtSimplex.RelStruct₀
      (pinchedNormalizedPointed (s - t) c.difference_proper_zero) .const where
  map := SSet.yonedaEquiv.symm c.normalizedFiller.toPinched
  δ_castSucc_map := by
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    apply congrArg SSet.yonedaEquiv.symm
    exact c.normalizedFiller_face 0
  δ_succ_map := by
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact (congrArg SSet.yonedaEquiv.symm (c.normalizedFiller_face 1)).trans
      (pinchedZeroSimplex_constant (n + 1))
  δ_map_of_lt j hj := by
    change j < 0 at hj
    exact (Fin.not_lt_zero j hj).elim
  δ_map_of_gt j hj := by
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    have hne : j ≠ 0 := by
      intro h
      subst j
      exact Fin.not_lt_zero _ hj
    have hf := c.normalizedFiller_face j
    rw [ite_eq_right hne] at hf
    exact (congrArg SSet.yonedaEquiv.symm hf).trans (pinchedZeroSimplex_constant (n + 1))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
