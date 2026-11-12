module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDegenerateTriangleOverlap

/-! # 全二単体充填の退化整合的な正規化

概要：退化二単体の充填を標準三単体へ置き換え、元の全四面と二つの退化式を保つ。
方針：二つの退化像を順に判定し、重なりの標準値の一致を使う。
規約：非退化の場合の元の充填を保つ。使われ方：有限二次図式の全退化整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)

variable (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

variable (U : K _⦋2⦌ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌)

/-- 退化二単体は標準三単体、それ以外は元の実充填を選ぶ。 -/
def dgVerdierNormalizeTriangleCone (σ : K _⦋2⦌) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌ := by
  classical
  exact if σ = K.σ 0 (K.δ 0 σ) then
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0 (K.δ 0 σ)
  else if σ = K.σ 1 (K.δ 2 σ) then
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1 (K.δ 2 σ)
  else U σ

/-- 二つの基本退化像の外では、正規化は元の同じ実充填を保つ。 -/
lemma dgVerdierNormalizeTriangleCone_of_nondegenerate (σ : K _⦋2⦌)
    (h₀ : σ ≠ K.σ 0 (K.δ 0 σ)) (h₁ : σ ≠ K.σ 1 (K.δ 2 σ)) :
    dgVerdierNormalizeTriangleCone A D C H U σ = U σ := by
  classical
  simp only [dgVerdierNormalizeTriangleCone, ite_eq_right h₀, ite_eq_right h₁]

/-- 単位整合的な全辺錐に沿う充填の正規化は、元の全四面を厳密に保つ。 -/
lemma dgVerdierNormalizeTriangleCone_boundary
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge)
    (hU : ∀ σ, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H σ (U σ)) (σ : K _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H σ (dgVerdierNormalizeTriangleCone A D C H U σ) := by
  classical
  unfold dgVerdierNormalizeTriangleCone
  split_ifs with h₀ h₁
  · have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone_boundary A D C H hunit 0 (K.δ 0 σ)
    exact Eq.mp (congrArg (fun w => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H w
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0 (K.δ 0 σ))) h₀.symm) hb
  · have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone_boundary A D C H hunit 1 (K.δ 2 σ)
    exact Eq.mp (congrArg (fun w => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTriangleConeBoundary A D C H w
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1 (K.δ 2 σ))) h₁.symm) hb
  · exact hU σ

/-- 零番号退化の正規化は、辺錐の標準一番号退化を厳密に選ぶ。 -/
lemma dgVerdierNormalizeTriangleCone_degeneracy_zero (e : K _⦋1⦌) :
    dgVerdierNormalizeTriangleCone A D C H U (K.σ 0 e) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0 e := by
  classical
  have hv : K.δ 0 (K.σ 0 e) = e := K.δ_comp_σ_self_apply (0 : Fin 2) e
  have he : K.σ 0 e = K.σ 0 (K.δ 0 (K.σ 0 e)) := congrArg (K.σ (0 : Fin 2)) hv.symm
  unfold dgVerdierNormalizeTriangleCone
  rw [ite_eq_left he]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 0) hv

/-- 一番号退化の正規化も、辺錐の標準二番号退化を厳密に選ぶ。 -/
lemma dgVerdierNormalizeTriangleCone_degeneracy_one
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) (e : K _⦋1⦌) :
    dgVerdierNormalizeTriangleCone A D C H U (K.σ 1 e) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1 e := by
  classical
  unfold dgVerdierNormalizeTriangleCone
  split_ifs with h₀ h₁
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone_overlap A D C H hunit _ e h₀.symm
  · exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDegenerateTriangleCone A D C H 1)
      (K.δ_comp_σ_succ_apply (1 : Fin 2) e)
  · have hv : K.δ 2 (K.σ 1 e) = e := K.δ_comp_σ_succ_apply (1 : Fin 2) e
    exact (h₁ (congrArg (K.σ (1 : Fin 2)) hv.symm)).elim

/-- 正規化した全二単体充填は、二つの基本退化の両方と厳密に整合する。 -/
lemma dgVerdierNormalizeTriangleCone_degeneracy
    (hunit : ∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) (i : Fin 2) (e : K _⦋1⦌) :
    dgVerdierNormalizeTriangleCone A D C H U (K.σ i e) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ i.succ (H e).simplex := by
  fin_cases i
  · exact dgVerdierNormalizeTriangleCone_degeneracy_zero A D C H U e
  · exact dgVerdierNormalizeTriangleCone_degeneracy_one A D C H U hunit e

end SerrePositivity.InfinityCategories.Project.DerivedCategories
