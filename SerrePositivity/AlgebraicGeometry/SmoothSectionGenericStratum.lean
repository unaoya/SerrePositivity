module

public import SerrePositivity.AlgebraicGeometry.SmoothSectionComponentSpread
public import SerrePositivity.AlgebraicGeometry.LocalizationIdempotent
import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
概要：滑らかなアフィン射の切断を通る成分は、整な基底の稠密主開上で開閉部分になる。
方針：生成ファイバーの成分を冪等元で切り出し、局所化で降ろした後に各ファイバーを比較する。
規約：二段の主開はそれぞれの分母で指定する。
使われ方：各既約閉部分上の構成可能性の判定。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct nonZeroDivisors

/--
概要：アフィン射の切断を任意の基底代数に移す。
方針：テンソル底変換の普遍性で元の切断を延長する。
規約：基底変更先の代数をテンソル積の左に置く。
使われ方：基底の主開と生成ファイバーで切断の値を比較する。
-/
def baseChangeSection {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] (s : B →ₐ[A] A) : S ⊗[A] B →ₐ[S] S :=
  AlgHom.liftEquiv A S B S ((IsScalarTower.toAlgHom A A S).comp s)

/--
概要：整域上の滑らかなアフィン射の切断を通る成分は、稠密主開上で一つの冪等元の主開になる。
方針：生成ファイバーの冪等元を一つの分母で降ろし、切断を通る成分の広がりを適用する。
規約：最初の分母は冪等元の定義に使い、次の分母は各ファイバーの連結性に使う。
使われ方：Stacks 055N の滑らかなアフィン場合。
-/
theorem exists_generic_stratum_sectionComponent_eq_basicOpen
    {A B : Type u} {K : Type v} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] [Field K] [Algebra A K] [IsFractionRing A K]
    (s : B →ₐ[A] A) :
    ∃ (a : A) (_ : a ≠ 0) (e : Localization.Away a ⊗[A] B) (r : Localization.Away a),
      r ≠ 0 ∧ IsIdempotentElem e ∧
      ∀ (F : Type w) [Field F] [Algebra (Localization.Away a) F],
        algebraMap (Localization.Away a) F r ≠ 0 →
        connectedComponent ((sectionPointInTensor F (baseChangeSection s)).comap
          (Algebra.TensorProduct.comm (Localization.Away a) F
            (Localization.Away a ⊗[A] B)).toRingHom) =
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[Localization.Away a] e :
            F ⊗[Localization.Away a] (Localization.Away a ⊗[A] B)) : Set _) := by
  let T := K ⊗[A] B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  let vK : T →ₐ[K] K := baseChangeSection s
  let p := (⊥ : PrimeSpectrum K).comap vK.toRingHom
  obtain ⟨d, hd, hComp⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace p)
  have hvd : vK d ≠ 0 := by
    have hp : p ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum T)) :=
      hComp ▸ mem_connectedComponent
    have hn := (PrimeSpectrum.mem_basicOpen _ _).mp hp
    exact fun h => hn (Ideal.mem_bot.mpr h)
  let M := Algebra.algebraMapSubmonoid B A⁰
  obtain ⟨⟨b, hb⟩, e₀, he₀, h₀⟩ := exists_idempotent_away_of_isLocalization M d hd
  obtain ⟨a, ha, rfl⟩ := hb
  have ha₀ : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
  let S := Localization.Away a
  let D := S ⊗[A] B
  let : IsDomain S := Localization.Away.isDomain ha₀
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let sK : S →+* K := IsLocalization.Away.lift a (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))
  let : Algebra S K := sK.toAlgebra
  let : IsScalarTower A S K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq a _ x).symm
  let : IsFractionRing S K := IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers a) S K (powers_le_nonZeroDivisors_of_noZeroDivisors ha₀)
  let eB : D ≃ₐ[B] Localization.Away (algebraMap A B a) :=
    IsLocalization.Away.tensorRightEquiv B a S
  let e := eB.symm e₀
  have he : IsIdempotentElem e := he₀.map eB.symm
  let cancel := Algebra.TensorProduct.cancelBaseChange A S K K B
  let j : D →+* T := cancel.toRingHom.comp
    (Algebra.TensorProduct.includeRight : D →ₐ[S] K ⊗[S] D).toRingHom
  let j₀ : Localization.Away (algebraMap A B a) →+* T :=
    IsLocalization.Away.lift (g := algebraMap B T) (algebraMap A B a)
      (IsLocalization.map_units T (⟨algebraMap A B a, ⟨a, ha, rfl⟩⟩ : M))
  have hj : j = j₀.comp eB.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A B a))
    ext x
    change cancel (1 ⊗ₜ[S] ((1 : S) ⊗ₜ[A] x)) = j₀ (eB (algebraMap B D x))
    rw [eB.commutes, IsLocalization.Away.lift_eq]
    simp [cancel]
    rfl
  have hje : j e = d := by
    rw [hj]
    change j₀ (eB (eB.symm e₀)) = d
    rw [eB.apply_symm_apply]
    exact h₀
  let v : D →ₐ[S] S := baseChangeSection s
  have hv (x : D) : vK (j x) = sK (v x) := by
    induction x using TensorProduct.inductionOn with
    | tmul y z =>
      change vK (cancel (1 ⊗ₜ[S] (y ⊗ₜ[A] z))) = sK (v (y ⊗ₜ[A] z))
      have hCancel : cancel (1 ⊗ₜ[S] (y ⊗ₜ[A] z)) = (algebraMap S K y) ⊗ₜ[A] z := by
        simp [cancel, Algebra.smul_def]
      rw [hCancel]
      change algebraMap S K y * algebraMap A K (s z) = sK (y * algebraMap A S (s z))
      rw [map_mul]
      exact congrArg (algebraMap S K y * ·) (IsScalarTower.algebraMap_apply A S K (s z))
    | add x y hx hy => simp [map_add, hx, hy]
  have hve : v e = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp (he.map v)).resolve_left (fun hz =>
      hvd (by rw [← hje, hv, hz, map_zero]))
  let z : K ⊗[S] D := 1 ⊗ₜ[S] e
  have hz : cancel z = d := hje
  let eLoc := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers z)
    (T := Submonoid.powers d) (Localization.Away z) (Localization.Away d)
    cancel.toRingEquiv (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hz)
  let : ConnectedSpace (PrimeSpectrum (Localization.Away d)) := by
    let h := (PrimeSpectrum.localization_away_isOpenEmbedding
      (Localization.Away d) d).isEmbedding.toHomeomorph
    rw [h.connectedSpace_iff, ← isConnected_iff_connectedSpace]
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away d) d, ← hComp]
    exact isConnected_connectedComponent
  let : ConnectedSpace (PrimeSpectrum (Localization.Away z)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv eLoc).connectedSpace_iff.mpr inferInstance
  let eTensor := IsLocalization.Away.tensorProductEquivTMulRight S K e (Localization.Away e)
  let : ConnectedSpace (PrimeSpectrum (K ⊗[S] Localization.Away e)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv eTensor.toRingEquiv).connectedSpace_iff.mpr inferInstance
  obtain ⟨r, hr, hSpread⟩ :=
    exists_nonzero_forall_sectionComponent_eq_basicOpen_of_smooth (K := K) v e he hve
  exact ⟨a, ha₀, e, r, hr, he, hSpread⟩

end SerrePositivity.AlgebraicGeometry
