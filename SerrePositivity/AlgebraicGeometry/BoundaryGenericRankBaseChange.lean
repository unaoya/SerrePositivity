module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryGenericRankLocalization
public import SerrePositivity.AlgebraicGeometry.BoundaryFlatBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の境界外一般階数の任意の基底変更。
方針：両側を元の代数の局所階数へ書き換え、拡大素点の縮約と自由性で照合する。
規約：元の加群の平坦性は境界外だけで仮定する。
使われ方：階数部分を分離した実チャートで、実際の加群の境界外一般階数を一定にする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外で相対平坦な有限加群の境界外一般階数は任意の基底変更で引き戻される。
方針：境界外の平坦性を基底変更し、各辺を自由な一般点での元の加群の局所階数として比較する。
規約：KST §5、Stacks 0810・0811、実分裂を入力し、係数環は Noether とする。
使われ方：階数一定化の中心のチャートで一定一般階数の係数中心の定理を使う。
-/
theorem boundaryGenericRank_baseChange
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)]
    (P : PrimeSpectrum (Localization.Away (algebraMap A C f))) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    boundaryGenericRank C D (D ⊗[B] M) (algebraMap A C f) P =
      boundaryGenericRank A B M f
        (PrimeSpectrum.comap (Localization.awayMap (algebraMap A C) f) P) := by
  dsimp only
  let F := Localization.Away f
  let L := Localization.Away (algebraMap A C f)
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let : Module.Flat L (L ⊗[C] (D ⊗[B] M)) :=
    flat_tensorAlgebra_away_of_boundary_flat A C M B f
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  let P₀ := PrimeSpectrum.comap (Localization.awayMap (algebraMap A C) f) P
  let P_C := PrimeSpectrum.comap (algebraMap C L) P
  let Q := geometricallyIntegralGenericPrime C D P_C
  have hbase : PrimeSpectrum.comap (algebraMap A C) P_C =
      PrimeSpectrum.comap (algebraMap A F) P₀ := by
    apply PrimeSpectrum.ext
    ext x
    change algebraMap C L (algebraMap A C x) ∈ P.asIdeal ↔
      (Localization.awayMap (algebraMap A C) f) (algebraMap A F x) ∈ P.asIdeal
    have h := IsLocalization.map_eq (M := Submonoid.powers f) (S := F)
      (T := Submonoid.powers (algebraMap A C f)) (Q := L) (g := algebraMap A C)
      (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) x
    exact h.symm ▸ Iff.rfl
  have hQ : Q.comap (algebraMap B D) =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A F) P₀) := by
    have h := geometricallyIntegralGenericPrime_baseChange_comap A B C e p hpe P_C
    exact h.trans (congrArg (geometricallyIntegralGenericPrime A B) hbase)
  have hfree : Q.comap (algebraMap B D) ∈ Module.freeLocus B M := by
    rw [hQ]
    exact genericPrime_mem_freeLocus_of_boundary_flat A B M e p hpe f P₀
  rw [boundaryGenericRank_eq_original_rankAtStalk C D (D ⊗[B] M) e' p' hs,
    boundaryGenericRank_eq_original_rankAtStalk A B M e p hpe]
  exact (rankAtStalk_baseChange_of_mem_freeLocus Q hfree).trans
    (congrArg (Module.rankAtStalk M) hQ)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
