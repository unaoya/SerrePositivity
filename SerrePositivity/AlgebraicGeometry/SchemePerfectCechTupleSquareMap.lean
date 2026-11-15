module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquare

/-!
概要：同じ nerve の実際の係数の写像は、同じ四角形の全ての辺を保つ。
方針：検証済みの引き戻しと増大写像の自然性を、既存の四角形の射へ渡す。
規約：基底・中心の係数と商を固定する。
使われ方：F8 の全複体を同じ可換な余単体図式にまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u v

namespace CechAugmentedSquare.Map
/-- 同じ四角形の二つの射は、四つの実際の成分が等しければ等しい。 -/
theorem ext_components {A : Type v} [CommRing A] {s t : CechAugmentedSquare.{u} A}
    (m n : CechAugmentedSquare.Map s t) (hl : m.left = n.left) (hr : m.right = n.right)
    (hb : m.base = n.base) (hc : m.center = n.center) : m = n := by
  cases m
  cases n
  cases hl
  cases hr
  cases hb
  cases hc
  rfl
end CechAugmentedSquare.Map

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の二つの係数関手の写像を持つ、四角形の自然な射。 -/
def schemePerfectCechTupleSquare_map {m n : SimplexCategory} (a : m ⟶ n) :
    CechAugmentedSquare.Map (schemePerfectCechTupleSquare f g F q hq U p hp hR hS m)
      (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n) where
  left := schemePerfectCechTupleMap g U p hp (schemeCechNervePresheaf_primeCast g p hR) a
  right := schemePerfectCechTupleMap f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
    (schemeCechNervePresheaf_primeCast f p hS) a
  base := LinearMap.id
  center := LinearMap.id
  restriction := by
    change schemePerfectCechTuplePullbackMap F U p hp
        (schemeCechNervePresheaf_primeCast f p hS) (schemeCechNervePresheaf_primeCast g p hR) m ≫
        schemePerfectCechTupleMap f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
          (schemeCechNervePresheaf_primeCast f p hS) a =
      schemePerfectCechTupleMap g U p hp (schemeCechNervePresheaf_primeCast g p hR) a ≫
        schemePerfectCechTuplePullbackMap F U p hp
          (schemeCechNervePresheaf_primeCast f p hS) (schemeCechNervePresheaf_primeCast g p hR) n
    exact (schemePerfectCechTuplePullback_naturality F U p hp
      (schemeCechNervePresheaf_primeCast f p hS) (schemeCechNervePresheaf_primeCast g p hR) a).symm
  scalar := by
    change ((schemePerfectCechTupleMap g U p hp
      (schemeCechNervePresheaf_primeCast g p hR) a).f 0).hom.comp
        (schemePerfectCechTupleAugmentation g U p hp hR m) =
      (schemePerfectCechTupleAugmentation g U p hp hR n).comp LinearMap.id
    rw [LinearMap.comp_id]
    exact schemePerfectCechTupleAugmentation_naturality g U p hp hR a
  quotient := by
    change LinearMap.id.comp (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap =
      (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap.comp LinearMap.id
    simp only [LinearMap.id_comp, LinearMap.comp_id]
  center_naturality := by
    change ((schemePerfectCechTupleMap f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
      (schemeCechNervePresheaf_primeCast f p hS) a).f 0).hom.comp
        (schemePerfectCechTupleAugmentation f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS m) =
      (schemePerfectCechTupleAugmentation f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS n).comp LinearMap.id
    rw [LinearMap.comp_id]
    exact schemePerfectCechTupleAugmentation_naturality f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS a

end SerrePositivity.AlgebraicGeometry
