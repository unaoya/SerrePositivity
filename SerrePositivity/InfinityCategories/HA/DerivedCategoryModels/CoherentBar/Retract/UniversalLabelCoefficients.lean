module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelVertexSupport
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
/-!
概要：標準単体の恒等ラベルで Dold–Kan 正規化の普遍係数を定める。
方針：既存のラベル射影と始点支持を直接使い、非零の係数が始点を保つことを示す。
規約：Mathlib の射影・退化相殺の証明は複製しない。
使われ方：普遍的なラベル係数を実 dg 加群の始点保存作用へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan SSet
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R]

abbrev dgCoherentBarUniversalIdentity (n : ℕ) : (Δ[n] : SSet.{u}) _⦋n⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)

def dgCoherentBarUniversalStageCoefficients (n q : ℕ) :
    ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage R Δ[n] q).f n
    (ModuleCat.freeMk (R := R) (dgCoherentBarUniversalIdentity n))

def dgCoherentBarUniversalCoefficients (n : ℕ) :
    ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection R Δ[n]).f n
    (ModuleCat.freeMk (R := R) (dgCoherentBarUniversalIdentity n))

lemma dgCoherentBarUniversalCoefficients_eq_stage (n : ℕ) :
    dgCoherentBarUniversalCoefficients R n = dgCoherentBarUniversalStageCoefficients R n n := by
  unfold dgCoherentBarUniversalCoefficients dgCoherentBarUniversalStageCoefficients
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelProjection, PInfty_f]
  rfl

lemma dgCoherentBarUniversalStageCoefficients_based (n q : ℕ)
    (a : (Δ[n] : SSet.{u}) _⦋n⦌)
    (ha : dgCoherentBarUniversalStageCoefficients R n q a ≠ 0) : a 0 = 0 := by
  have hz : ModuleCat.freeMk (R := R) (dgCoherentBarUniversalIdentity n) ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelVertexSupport R Δ[n] n
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelFirstVertex Δ[n] (dgCoherentBarUniversalIdentity n)) := by
    exact Finsupp.single_mem_supported R 1 rfl
  have hp := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelStage_preserves_vertex_support R Δ[n] q n _ _ hz
  have hv := (Finsupp.mem_supported R _).1 hp (Finsupp.mem_support_iff.mpr ha)
  exact congrArg (fun v : (Δ[n] : SSet.{u}) _⦋0⦌ => v 0) hv

lemma dgCoherentBarUniversalCoefficients_based (n : ℕ)
    (a : (Δ[n] : SSet.{u}) _⦋n⦌) (ha : dgCoherentBarUniversalCoefficients R n a ≠ 0) : a 0 = 0 := by
  rw [dgCoherentBarUniversalCoefficients_eq_stage] at ha
  exact dgCoherentBarUniversalStageCoefficients_based R n n a ha

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
