module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedProperEquations

/-! # 閉分母による実 pinched Hom と線形境界の前合成

概要：元の閉射で pinched Hom を前合成し、全成分・削除右辺・真部分集合の方程式を保つ。
方針：全 Hom 鎖写像の成分を斉次前合成と同定し、線形表示の鎖写像の自然性を使う。
規約：面と退化を厳密に保つ。使われ方：商の境界を共通実分母の後で充填する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉射による pinched 線形データの前合成。 -/
def pinchedClosedPrecomposeData {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A q y n :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s) f

/-- 各成分は元の指定された斉次成分の前合成。 -/
lemma pinchedClosedPrecomposeData_component {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (pinchedClosedPrecomposeData A D s f).component J k hJ hk =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (f.component J k hJ hk) s := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f A D s k (f.component J k hJ hk)

/-- 削除右辺は同じ閉射の前合成と厳密に可換。 -/
lemma pinchedClosedPrecomposeData_rhs {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (pinchedClosedPrecomposeData A D s f).rhs J k hk =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) (f.rhs J k hk) s :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s) f J k hk).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f A D s (k + 1) (f.rhs J k hk))

/-- 全真部分集合の削除方程式は閉射の前合成で保たれる。 -/
lemma pinchedClosedPrecomposeData_proper_equations {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk) :
    ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A ((pinchedClosedPrecomposeData A D s f).component J k hJ hk) =
        (pinchedClosedPrecomposeData A D s f).rhs J k hk := by
  intro J k hJ hk hne
  rw [pinchedClosedPrecomposeData_component, pinchedClosedPrecomposeData_rhs]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k (k + 1) rfl (f.component J k hJ hk) s).trans
    (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s) (he J k hJ hk hne))

/-- 線形データの前合成は全ての面・退化の引き戻しと可換。 -/
lemma pinchedClosedPrecomposeData_pullback {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) :
    pinchedClosedPrecomposeData A D s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (pinchedClosedPrecomposeData A D s f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearDataMap_pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s) α f

/-- 元の閉射による、実際の pinched Hom の前合成写像。 -/
def pinchedClosedPrecomposition {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
