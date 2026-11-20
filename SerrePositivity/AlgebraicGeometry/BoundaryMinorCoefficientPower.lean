module

public import SerrePositivity.AlgebraicGeometry.GenericMinorCoefficientUnit
public import SerrePositivity.AlgebraicGeometry.BoundaryHigherMinorVanishing
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientBaseChange

/-!
概要：KST §5、Stacks 0810 の境界外の平坦性から係数中心の境界冪を選ぶ。
方針：境界外の係数イデアルの単位性を基底変更公式で戻し、局所化イデアルを判定する。
規約：境界外の一般階数を入力し、元の加群の基礎環上の平坦性は要求しない。
使われ方：元の開集合 D(f) に正確に適合する実際の係数 blowup 中心を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外で平坦で一定一般階数を持つ有限加群の小行列式の係数イデアルは境界の冪を含む。
方針：境界外での係数の単位性と局所化イデアルの単位性の判定を接続する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、境界元の正則性はこの冪の所属には不要。
使われ方：admissible な係数中心の補開集合を D(f) と同定する。
-/
theorem exists_pow_mem_minorCoefficient_of_boundary_genericRank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q) (H : Matrix m n B)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q) (f : A)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] (r : ℕ)
    (hrank :
      let F := Localization.Away f
      let D := F ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
        geometricallyIntegral_tensorProjection A B F
      ∀ P : PrimeSpectrum F,
        let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
        Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r) :
    ∃ N : ℕ, f ^ N ∈ splitAlgebraCoefficientIdeal e (matrixMinorIdeal H (Fintype.card m - r)) := by
  classical
  let F := Localization.Away f
  let D := F ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  let : Module.Flat F (D ⊗[B] M) := tensorAlgebraBaseChange_flat A B F M
  let e' := splitAlgebraTensorEmbedding (C := F) e
  let p' := splitAlgebraTensorRetraction (C := F) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  let qD := finiteFreePresentationBaseChange (C := D) q
  have hqD : Function.Surjective qD := finiteFreePresentationBaseChange_surjective q hq
  have hker := finiteFreePresentationBaseChange_columnSpan_eq_ker (C := D) H q hq hH
  have hrankD : ∀ P : PrimeSpectrum F,
      let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
      Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r := hrank
  let J := matrixMinorIdeal H (Fintype.card m - r)
  let I := splitAlgebraCoefficientIdeal e J
  have hunitD : splitAlgebraCoefficientIdeal e'
      (matrixMinorIdeal (H.map (algebraMap B D)) (Fintype.card m - r)) = ⊤ :=
    minorCoefficientIdeal_eq_top_of_constant_genericRank F D e' p' hs qD hqD
      (H.map (algebraMap B D)) hker r hrankD
  have hbase : splitAlgebraCoefficientIdeal e'
      (matrixMinorIdeal (H.map (algebraMap B D)) (Fintype.card m - r)) =
        I.map (algebraMap A F) := by
    rw [← matrixMinorIdeal_map]
    exact splitAlgebraCoefficientIdeal_baseChange e p hpe J
  have hmap : I.map (algebraMap A F) = ⊤ := hbase.symm.trans hunitD
  have hnot : ¬ Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (I : Set A) := by
    intro hd
    exact ((IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (M := Submonoid.powers f) (S := F) I).mpr hd) hmap
  obtain ⟨a, ha, hIa⟩ := Set.not_disjoint_iff.mp hnot
  obtain ⟨N, rfl⟩ := ha
  exact ⟨N, hIa⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
