module

public import SerrePositivity.AlgebraicGeometry.SmoothGeometricFiberSpreading
import SerrePositivity.AlgebraicGeometry.SmoothGeometricConnectedPoint
public import SerrePositivity.AlgebraicGeometry.SmoothSectionSpecialization
import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：生成ファイバーの連結成分を切り出す開閉部分は、基底を縮めた後も切断を通る連結成分になる。
方針：開閉部分の幾何学的整性を広げ、各ファイバーで切断を通ることを冪等元で確かめる。
規約：開閉部分は切断が一に送る冪等元で指定する。
使われ方：Stacks 055N の滑らかなアフィンの場合。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：切断を通る開閉部分の生成ファイバーが連結なら、
ある主開上の任意の体への底変換で、その部分は切断を通る連結成分に一致する。
方針：切断の有理点から生成ファイバーの幾何学的整性を得て、それを稠密主開へ広げる。
規約：体を左に置くテンソル積のスペクトル上で連結成分を比較する。
使われ方：既約な台の上で切断を通るファイバー成分が開閉になることを示す。
-/
theorem exists_nonzero_forall_sectionComponent_eq_basicOpen_of_smooth
    {A B : Type u} {K : Type v} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] [Field K] [Algebra A K] [IsFractionRing A K]
    (s : B →ₐ[A] A) (e : B) (he : IsIdempotentElem e) (hs : s e = 1)
    [ConnectedSpace (PrimeSpectrum (K ⊗[A] Localization.Away e))] :
    ∃ a : A, a ≠ 0 ∧ ∀ (F : Type w) [Field F] [Algebra A F], algebraMap A F a ≠ 0 →
      connectedComponent ((sectionPointInTensor F s).comap
        (Algebra.TensorProduct.comm A F B).toRingHom) =
        (PrimeSpectrum.basicOpen (1 ⊗ₜ[A] e : F ⊗[A] B) : Set (PrimeSpectrum (F ⊗[A] B))) := by
  let C := Localization.Away e
  let : Algebra.Smooth B C := Algebra.Smooth.of_isLocalization_Away e
  let : Algebra.Smooth A C := Algebra.Smooth.comp A B C
  let t : C →ₐ[A] A := IsLocalization.Away.liftAlgHom (S := C) e (f := s) (by simp [hs])
  let t₀ := (IsScalarTower.toAlgHom A A K).comp t
  let tK : K ⊗[A] C →ₐ[K] K := AlgHom.liftEquiv A K C K t₀
  let : IsDomain (AlgebraicClosure K ⊗[K] (K ⊗[A] C)) :=
    isDomain_tensor_of_connected_smooth_of_section tK
  obtain ⟨a, ha, hC⟩ :=
    exists_nonzero_forall_isDomain_tensor_of_smooth_generic (A := A) (K := K) (B := C)
  refine ⟨a, ha, ?_⟩
  intro F _ _ hF
  let D := F ⊗[A] B
  let eF : D := 1 ⊗ₜ[A] e
  let p := (sectionPointInTensor F s).comap (Algebra.TensorProduct.comm A F B).toRingHom
  have hIdem : IsIdempotentElem eF :=
    he.map (Algebra.TensorProduct.includeRight : B →ₐ[A] D)
  have hClopen : IsClopen (PrimeSpectrum.basicOpen eF : Set (PrimeSpectrum D)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨eF, hIdem, rfl⟩
  have hp : p ∈ (PrimeSpectrum.basicOpen eF : Set (PrimeSpectrum D)) := by
    apply (PrimeSpectrum.mem_basicOpen _ _).mpr
    change ¬ (sectionFiberEval s (e ⊗ₜ[A] (1 : F))) ∈ (⊥ : Ideal F)
    simp [sectionFiberEval, hs, Algebra.smul_def]
  let : IsDomain (F ⊗[A] C) := hC F hF
  let eC := IsLocalization.Away.tensorProductEquivTMulRight A F e C
  let : IsDomain (Localization.Away eF) :=
    Function.Injective.isDomain eC.symm.toRingHom eC.symm.injective
  have hConnected : IsConnected (PrimeSpectrum.basicOpen eF : Set (PrimeSpectrum D)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away eF) eF, ← Set.image_univ]
    exact isConnected_univ.image _ (PrimeSpectrum.continuous_comap _).continuousOn
  exact (hClopen.connectedComponent_subset hp).antisymm (hConnected.subset_connectedComponent hp)

end SerrePositivity.AlgebraicGeometry
