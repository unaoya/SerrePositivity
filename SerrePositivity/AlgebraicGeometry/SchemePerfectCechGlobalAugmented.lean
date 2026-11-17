module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmented

/-!
概要：同じ基底と実際のnerveの大域切断のFrobenius係数の増大図式。
方針：元の大域スカラーの自然性を有限段の元で照合する。
規約：Γ–Specの同型で基底を暗黙に置き換えない。
使われ方：元の基底環の増大を含むタプルČechの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 元の基底環から実際のnerve項のΓへのFrobenius係数写像。 -/
def schemePerfectCechGlobalScalar (n : SimplexCategory) :
    ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR) ⟶
      (frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
        (fun n ↦ schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))).obj n :=
  ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR
    (schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))).toAddMonoidHom.toIntLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- 同じ大域スカラーの係数写像は実際のnerveの射に自然。 -/
theorem schemePerfectCechGlobalScalar_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    schemePerfectCechGlobalScalar f p hp hR m ≫
        (frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
          (fun n ↦ schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))).map a =
      schemePerfectCechGlobalScalar f p hp hR n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨k, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap R p hp hR) z
  change frobeniusDirectLimitOf _ p hp _ k
      (((Arrow.mk f).cechNerve.map a.op).appTop.hom
        (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op m)) x)) =
    frobeniusDirectLimitOf _ p hp _ k
      (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)) x)
  exact congrArg (frobeniusDirectLimitOf _ p hp _ k)
    (RingHom.congr_fun (schemeCechNerveScalarHom_naturality f a.op) x).symm

/-- 元の基底と同じ実際のΓ係数からなる増大余単体図式。 -/
def schemePerfectCechGlobalAugmented : CosimplicialObject.Augmented (ModuleCat.{u} ℤ) where
  left := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  right := frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
    (fun n ↦ schemeCechNervePresheaf_primeCast f p hR (op n) (op ⊤))
  hom :=
    { app := schemePerfectCechGlobalScalar f p hp hR
      naturality := fun {m n} a ↦ by
        change 𝟙 _ ≫ schemePerfectCechGlobalScalar f p hp hR n = _
        rw [Category.id_comp]
        exact (schemePerfectCechGlobalScalar_naturality f p hp hR a).symm }

/-- 同じΓの増大図式に既存のsingle関手を施した値。 -/
def schemePerfectCechGlobalSingleAugmented :
    CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  (CosimplicialObject.Augmented.whiskeringObj _ _
    (HomologicalComplex.single (ModuleCat.{u} ℤ) (.up ℕ) 0)).obj
      (schemePerfectCechGlobalAugmented f p hp hR)

end SerrePositivity.AlgebraicGeometry
