module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcIntervalOverlap

/-!
概要：指定した区間のtensorを、局所化・商・交わりの区間環へ比較する。
方針：元の区間環の普遍性で両方向の射を作り、基底上の射の一意性で両逆を示す。
規約：端点・元の係数と構造射を保つ。被約性・Noether性や新しい区間の選択を仮定しない。
使われ方：2iのO01〜O03、BM18 Proposition 4.8(5)の和の上での三つの係数の照合。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O01：同じ端点の区間の係数の標準比較。 -/
def intervalTensorLocalizationEquiv {V : Type u} [CommRing V]
    {a b d : PrimeSpectrum V} (hab : a ≤ b) (hbd : b ≤ d) :
    ValuationIntervalRing (hab.trans hbd) ⊗[V] Localization.AtPrime b.asIdeal
      ≃ₐ[V] ValuationIntervalRing hab := by
  let had := hab.trans hbd
  let P := ValuationIntervalRing had ⊗[V] Localization.AtPrime b.asIdeal
  let iL : ValuationIntervalRing had →ₐ[V] P := Algebra.TensorProduct.includeLeft
  let iR : Localization.AtPrime b.asIdeal →ₐ[V] P := Algebra.TensorProduct.includeRight
  let left : ValuationIntervalRing had →ₐ[V] ValuationIntervalRing hab :=
    { toRingHom := intervalRingMap had hab le_rfl hbd
      commutes' := intervalRingMap_algebraMap had hab le_rfl hbd }
  let F : P →ₐ[V] ValuationIntervalRing hab := Algebra.TensorProduct.lift left
    (Arc.localizationToInterval hab) (fun _ _ ↦ Commute.all _ _)
  have hkill (x : V) (hx : x ∈ a.asIdeal) : algebraMap V P x = 0 := by
    rw [← iL.commutes x, intervalRing_map_eq_zero had hx, map_zero]
  have hunit (x : V) (hx : x ∉ b.asIdeal) : IsUnit (algebraMap V P x) := by
    rw [← iR.commutes x]
    exact (IsLocalization.map_units (M := b.asIdeal.primeCompl)
      (Localization.AtPrime b.asIdeal) ⟨x, hx⟩).map iR.toRingHom
  let G : ValuationIntervalRing hab →ₐ[V] P :=
    { toRingHom := intervalRingLift hab (algebraMap V P) hkill hunit
      commutes' := intervalRingLift_algebraMap hab (algebraMap V P) hkill hunit }
  have uniq {X : Type u} [CommRing X] [Algebra V X] {c d : PrimeSpectrum V}
      (h' : c ≤ d) (u v : ValuationIntervalRing h' →ₐ[V] X) : u = v := by
    apply AlgHom.toRingHom_injective
    exact intervalRing_hom_ext h' (fun x ↦ (u.commutes x).trans (v.commutes x).symm)
  have locUniq {X : Type u} [CommRing X] [Algebra V X]
      (u v : Localization.AtPrime b.asIdeal →ₐ[V] X) : u = v := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext b.asIdeal.primeCompl
    apply RingHom.ext
    intro x
    exact (u.commutes x).trans (v.commutes x).symm
  refine AlgEquiv.ofAlgHom F G (uniq hab _ _) ?_
  apply Algebra.TensorProduct.ext
  · exact uniq had _ _
  · exact locUniq _ _

/-- 計画O02：同じ端点の区間の係数の標準比較。 -/
def intervalTensorQuotientEquiv {V : Type u} [CommRing V]
    {a c d : PrimeSpectrum V} (hac : a ≤ c) (hcd : c ≤ d) :
    ValuationIntervalRing (hac.trans hcd) ⊗[V] (V ⧸ c.asIdeal)
      ≃ₐ[V] ValuationIntervalRing hcd := by
  let had := hac.trans hcd
  let Q := V ⧸ c.asIdeal
  let P := ValuationIntervalRing had ⊗[V] Q
  let iL : ValuationIntervalRing had →ₐ[V] P := Algebra.TensorProduct.includeLeft
  let iR : Q →ₐ[V] P := Algebra.TensorProduct.includeRight
  let left : ValuationIntervalRing had →ₐ[V] ValuationIntervalRing hcd :=
    { toRingHom := intervalRingMap had hcd hac le_rfl
      commutes' := intervalRingMap_algebraMap had hcd hac le_rfl }
  let F : P →ₐ[V] ValuationIntervalRing hcd := Algebra.TensorProduct.lift left
    (IsScalarTower.toAlgHom V Q (ValuationIntervalRing hcd)) (fun _ _ ↦ Commute.all _ _)
  have hkill (x : V) (hx : x ∈ c.asIdeal) : algebraMap V P x = 0 := by
    rw [← iR.commutes x]
    change iR (Ideal.Quotient.mk c.asIdeal x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hunit (x : V) (hx : x ∉ d.asIdeal) : IsUnit (algebraMap V P x) := by
    rw [← iL.commutes x]
    exact (intervalRing_isUnit had hx).map iL.toRingHom
  let G : ValuationIntervalRing hcd →ₐ[V] P :=
    { toRingHom := intervalRingLift hcd (algebraMap V P) hkill hunit
      commutes' := intervalRingLift_algebraMap hcd (algebraMap V P) hkill hunit }
  have uniq {X : Type u} [CommRing X] [Algebra V X] {c d : PrimeSpectrum V}
      (h' : c ≤ d) (u v : ValuationIntervalRing h' →ₐ[V] X) : u = v := by
    apply AlgHom.toRingHom_injective
    exact intervalRing_hom_ext h' (fun x ↦ (u.commutes x).trans (v.commutes x).symm)
  have quotUniq {X : Type u} [CommRing X] [Algebra V X] (u v : Q →ₐ[V] X) : u = v := by
    apply AlgHom.ext
    intro x
    obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (u.commutes x0).trans (v.commutes x0).symm
  refine AlgEquiv.ofAlgHom F G (uniq hcd _ _) ?_
  apply Algebra.TensorProduct.ext
  · exact uniq had _ _
  · exact quotUniq _ _

/-- 計画O03：同じ端点の区間の係数の標準比較。 -/
def intervalTensorIntersectionEquiv {V : Type u} [CommRing V]
    {a c b d : PrimeSpectrum V} (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d) :
    ValuationIntervalRing (hac.trans (hcb.trans hbd)) ⊗[V] ValuationIntervalRing hcb
      ≃ₐ[V] ValuationIntervalRing hcb := by
  let had := hac.trans (hcb.trans hbd)
  let P := ValuationIntervalRing had ⊗[V] ValuationIntervalRing hcb
  let left : ValuationIntervalRing had →ₐ[V] ValuationIntervalRing hcb :=
    { toRingHom := intervalRingMap had hcb hac hbd
      commutes' := intervalRingMap_algebraMap had hcb hac hbd }
  let F : P →ₐ[V] ValuationIntervalRing hcb := Algebra.TensorProduct.lift left
    (AlgHom.id V (ValuationIntervalRing hcb)) (fun _ _ ↦ Commute.all _ _)
  let G : ValuationIntervalRing hcb →ₐ[V] P := Algebra.TensorProduct.includeRight
  have uniq {X : Type u} [CommRing X] [Algebra V X] {c d : PrimeSpectrum V}
      (h' : c ≤ d) (u v : ValuationIntervalRing h' →ₐ[V] X) : u = v := by
    apply AlgHom.toRingHom_injective
    exact intervalRing_hom_ext h' (fun x ↦ (u.commutes x).trans (v.commutes x).symm)
  refine AlgEquiv.ofAlgHom F G (uniq hcb _ _) ?_
  apply Algebra.TensorProduct.ext
  · exact uniq had _ _
  · exact uniq hcb _ _

end SerrePositivity.AlgebraicGeometry.ArcRouteB
