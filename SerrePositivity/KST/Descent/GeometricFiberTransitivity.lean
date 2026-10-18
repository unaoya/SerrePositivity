module

public import SerrePositivity.KST.Descent.CommonGeometricPoints
public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# 幾何ファイバーの推移性から通常のファイバーの推移性へ

## 概要
既存の環論的な幾何的推移性を、同じ基底点上の素イデアルの推移性へ移す。

## 方針
共通の代数閉体上へ持ち上げた二点にテンソル積上の推移性を適用し、左因子へ戻す。

## 規約
幾何的推移性の定義を変更しない。群元の向きは既存の comap の定義を保持する。

## 使われ方
論文 定理 3.1 の移動切断の像の被覆条件。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace SerrePositivity.KST.Descent

variable {A T G : Type u} [CommRing A] [CommRing T] [Algebra A T] [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：代数閉体上の二つの点の像は幾何的推移性で結ばれる（論文 定理 3.1）。
方針：二つの代数射をテンソル積からの射に拡張し、指定推移性を左因子へ射影する。
規約：同じ A 代数構造を持つ体への二つの射を比較する。
使われ方：共通の幾何点の像を通常の素イデアルとして比較する。 -/
theorem geometricTransitivity_comap_pair (transitive : IsGeometricallyTransitive A T G)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω]
    (a b : T →ₐ[A] Ω) (t : PrimeSpectrum Ω) :
    ∃ g : G, PrimeSpectrum.comap (MulSemiringAction.toRingHom G T g)
      (PrimeSpectrum.comap a.toRingHom t) = PrimeSpectrum.comap b.toRingHom t := by
  let liftA := Algebra.TensorProduct.lift a (AlgHom.id A Ω) (fun _ _ ↦ Commute.all _ _)
  let liftB := Algebra.TensorProduct.lift b (AlgHom.id A Ω) (fun _ _ ↦ Commute.all _ _)
  obtain ⟨g, hg⟩ := transitive Ω (PrimeSpectrum.comap liftA.toRingHom t)
    (PrimeSpectrum.comap liftB.toRingHom t)
  refine ⟨g, ?_⟩
  have project := congrArg
    (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom) hg
  have hA : liftA.toRingHom.comp
      ((tensorAction A T G Ω g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom) =
      a.toRingHom.comp (MulSemiringAction.toRingHom G T g) := by
    ext x
    simp [liftA, tensorAction]
  have hB : liftB.toRingHom.comp
      (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom = b.toRingHom := by
    ext x
    simp [liftB]
  change PrimeSpectrum.comap (liftA.toRingHom.comp
      ((tensorAction A T G Ω g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom)) t =
    PrimeSpectrum.comap (liftB.toRingHom.comp
      (Algebra.TensorProduct.includeLeft : T →ₐ[A] T ⊗[A] Ω).toRingHom) t at project
  rw [hA, hB] at project
  exact project

/-- 概要：既存の幾何的推移性から同じ基底点上の素イデアルは群元で結ばれる（定理 3.1）。
方針：共通の代数閉体上の二点を選び、Spec の充満忠実性で代数射へ移して比較する。
規約：元の A・T・G と既存の幾何的推移性の定義を使い、有限性は不要。
使われ方：Spec T 上の移動切断の像の被覆を供給するための点の推移性。 -/
theorem geometricTransitivity_on_fibers (transitive : IsGeometricallyTransitive A T G)
    (x y : PrimeSpectrum T)
    (same_base : PrimeSpectrum.comap (algebraMap A T) x =
      PrimeSpectrum.comap (algebraMap A T) y) :
    ∃ g : G, PrimeSpectrum.comap (MulSemiringAction.toRingHom G T g) x = y := by
  classical
  let p : Spec (.of T) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A T))
  obtain ⟨Ω, field, closed, a, b, hab, t, ha, hb⟩ :=
    exists_common_geometric_points p p x y same_base
  let := field
  let := closed
  let φ : T →+* Ω := (Spec.preimage a).hom
  let ψ : T →+* Ω := (Spec.preimage b).hom
  have hcat : CommRingCat.ofHom (algebraMap A T) ≫ Spec.preimage a =
      CommRingCat.ofHom (algebraMap A T) ≫ Spec.preimage b := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage] using hab
  have hcomp : φ.comp (algebraMap A T) = ψ.comp (algebraMap A T) :=
    congrArg (fun k ↦ k.hom) hcat
  let : Algebra A Ω := (φ.comp (algebraMap A T)).toAlgebra
  let aa : T →ₐ[A] Ω := { φ with commutes' := fun _ ↦ rfl }
  let bb : T →ₐ[A] Ω := { ψ with commutes' := fun r ↦ (RingHom.congr_fun hcomp r).symm }
  have hφ : PrimeSpectrum.comap φ t = x :=
    (congrArg (fun k : Spec (.of Ω) ⟶ Spec (.of T) ↦ k t) (Spec.map_preimage a)).trans ha
  have hψ : PrimeSpectrum.comap ψ t = y :=
    (congrArg (fun k : Spec (.of Ω) ⟶ Spec (.of T) ↦ k t) (Spec.map_preimage b)).trans hb
  obtain ⟨g, hg⟩ := geometricTransitivity_comap_pair transitive Ω aa bb t
  exact ⟨g, (congrArg (PrimeSpectrum.comap (MulSemiringAction.toRingHom G T g)) hφ).symm.trans
    (hg.trans hψ)⟩

end SerrePositivity.KST.Descent
