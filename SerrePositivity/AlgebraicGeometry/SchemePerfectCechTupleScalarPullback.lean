module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleNaturality
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechAugmentationComposition

/-!
概要：同じ二つの係数関手の引き戻しは、基底環の射の増大写像を保つ。
方針：同じ nerve の基底への射の可換性と既存のスカラーの合成則を使う。
規約：元の基底環の写像と実際の切断の写像を保つ。
使われ方：閉中心の商の辺を、同じ四角形の増大軸に接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))

include hq in
set_option backward.isDefEq.respectTransparency false in
/-- 実際の nerve の引き戻しは、同じ基底環の射に沿う大域スカラーを保つ。 -/
theorem schemeCechNerveMapScalarHom_naturality (n : SimplexCategoryᵒᵖ) :
    ((Arrow.mapCechNerve F).app n).appTop.hom.comp
      (schemeScalarHom _ ((Arrow.mk g).augmentedCechNerve.hom.app n)) =
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app n)).comp q := by
  have hw : (Arrow.mapCechNerve F).app n ≫
      (Arrow.mk g).augmentedCechNerve.hom.app n =
      (Arrow.mk f).augmentedCechNerve.hom.app n ≫ Spec.map (CommRingCat.ofHom q) := by
    change WidePullback.lift
        (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f) ≫ F.right)
        (fun i : Fin (n.unop.len + 1) ↦
          WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) i ≫ F.left) _ ≫
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f) ≫ _
    exact (WidePullback.lift_base _ _ _ _).trans
      (congrArg (fun k : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) ↦
        WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f) ≫ k) hq)
  exact (schemeScalarHom_naturality _ ((Arrow.mapCechNerve F).app n)
    ((Arrow.mk g).augmentedCechNerve.hom.app n)
    ((Arrow.mk f).augmentedCechNerve.hom.app n) q hw).symm

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

include hq in
set_option backward.isDefEq.respectTransparency false in
/-- 同じ引き戻しと二つの増大写像は、基底の Frobenius の係数写像と可換。 -/
theorem schemePerfectCechTuplePullback_augmentation (n : SimplexCategory) :
    ((schemePerfectCechTuplePullbackMap F U p hp
      (schemeCechNervePresheaf_primeCast f p hS)
      (schemeCechNervePresheaf_primeCast g p hR) n).f 0).hom.comp
        (schemePerfectCechTupleAugmentation g U p hp hR n) =
      (schemePerfectCechTupleAugmentation f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS n).comp
        (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  have h := schemeStructurePerfectCechRefinedPullbackMap_augmentation
    ((Arrow.mapCechNerve F).app (op n))
    (schemeScalarHom _ ((Arrow.mk g).augmentedCechNerve.hom.app (op n)))
    ((schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n))).comp q)
    (schemeCechNerveMapScalarHom_naturality f g F q hq (op n)).symm p hp hR
    (schemeCechNervePresheaf_primeCast g p hR (op n))
    (schemeCechNervePresheaf_primeCast f p hS (op n))
    (schemeCechTupleOpen g U (op n))
    (schemeCechTupleOpen f (fun i ↦ F.left ⁻¹ᵁ U i) (op n)) id
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))
  exact h.trans (schemeStructurePerfectCechAugmentation_comp
    ((Arrow.mk f).cechNerve.obj (op n))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n))) q p hp hR hS
    (schemeCechNervePresheaf_primeCast f p hS (op n))
    (schemeCechTupleOpen f (fun i ↦ F.left ⁻¹ᵁ U i) (op n)))

end SerrePositivity.AlgebraicGeometry
