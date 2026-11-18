module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmented
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleScalarPullback

/-!
概要：基底環の射に沿う実際の引き戻しは、同じ増大余単体図式の射となる。
方針：既存の single からの射の零次成分の外延性と、実際の増大写像の可換性を使う。
規約：基底の係数写像・同じ被覆・全ての nerve の射を保つ。
使われ方：同じ閉中心の四角形を増大軸を含む図式で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

include hq in
set_option backward.isDefEq.respectTransparency false in
/-- 同じ single からの二つの増大写像は、実際の基底の係数写像と可換。 -/
theorem schemePerfectCechTupleAugmentationHom_pullback (n : SimplexCategory) :
    schemePerfectCechTupleAugmentationHom g U p hp hR n ≫
        schemePerfectCechTuplePullbackMap F U p hp
          (schemeCechNervePresheaf_primeCast f p hS)
          (schemeCechNervePresheaf_primeCast g p hR) n =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).map
        (ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap) ≫
          schemePerfectCechTupleAugmentationHom f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS n := by
  apply HomologicalComplex.from_single_hom_ext
  have h0 : ModuleCat.ofHom (schemePerfectCechTupleAugmentation g U p hp hR n) ≫
      (schemePerfectCechTuplePullbackMap F U p hp
        (schemeCechNervePresheaf_primeCast f p hS)
        (schemeCechNervePresheaf_primeCast g p hR) n).f 0 =
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap ≫
        ModuleCat.ofHom (schemePerfectCechTupleAugmentation f
          (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS n) := by
    apply ModuleCat.hom_ext
    exact schemePerfectCechTuplePullback_augmentation f g F q hq U p hp hR hS n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    schemePerfectCechTupleAugmentationHom_f_zero,
    schemePerfectCechTupleAugmentationHom_f_zero, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
    (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫ k) h0

set_option backward.isDefEq.respectTransparency false in
/-- 基底・係数・増大写像を保つ、同じ増大余単体図式の実際の射。 -/
def schemePerfectCechTupleAugmentedPullback :
    schemePerfectCechTupleAugmented g U p hp hR ⟶
      schemePerfectCechTupleAugmented f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS where
  left := (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).map
    (ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap)
  right := schemePerfectCechTuplePullback F U p hp
    (schemeCechNervePresheaf_primeCast f p hS) (schemeCechNervePresheaf_primeCast g p hR)
  w := by
    apply NatTrans.ext
    funext n
    exact (schemePerfectCechTupleAugmentationHom_pullback f g F q hq U p hp hR hS n).symm

end SerrePositivity.AlgebraicGeometry
