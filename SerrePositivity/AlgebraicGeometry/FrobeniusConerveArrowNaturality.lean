module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConervePerfectNaturality
public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowNaturality

/-!
概要：同じ conerve の Frobenius の標準比較は、元の環の可換な四角形に自然。
方針：同じ標準脚の可換性を既存の conerve 関手で写し、有限段で評価する。
規約：元の四角形と実際の Frobenius の矢印の写像を保つ。
使われ方：有限型模型と filtered な図式の射への係数比較の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {f g : Arrow CommRingCat.{u}} (F : f ⟶ g) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
variable (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の標準比較は、元の環の可換な四角形の conerve の各環準同型に自然。 -/
theorem frobeniusConervePerfectIso_arrow_naturality (n : SimplexCategory) :
    CommRingCat.ofHom (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast g p hC n)
        ((Arrow.mapCechConerve F).app n).hom) ≫
      (frobeniusConervePerfectIso g p hp hC hD n).hom =
    (frobeniusConervePerfectIso f p hp hA hB n).hom ≫
      (Arrow.mapCechConerve (frobeniusDirectLimitArrowMap F p hp hA hB hC hD)).app n := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) z
  change (frobeniusConervePerfectIso g p hp hC hD n).hom.hom
      (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast g p hC n)
        ((Arrow.mapCechConerve F).app n).hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x)) =
    ((Arrow.mapCechConerve (frobeniusDirectLimitArrowMap F p hp hA hB hC hD)).app n).hom
      ((frobeniusConervePerfectIso f p hp hA hB n).hom.hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x))
  rw [frobeniusDirectLimitMap_of, frobeniusConervePerfectIso_of, frobeniusConervePerfectIso_of]
  have h : (frobeniusArrowCocone f p hp hA hB).ι.app i ≫
      frobeniusDirectLimitArrowMap F p hp hA hB hC hD =
        F ≫ (frobeniusArrowCocone g p hp hC hD).ι.app i :=
    frobeniusArrowCocone_map F p hp hA hB hC hD (ULift.up i)
  have h' := congrArg (fun k ↦ CosimplicialObject.cechConerve.map k) h
  rw [Functor.map_comp, Functor.map_comp] at h'
  have hn := congr_app h' n
  simp only [NatTrans.comp_app] at hn
  exact (congrArg (fun k ↦ k.hom x) hn).symm

end SerrePositivity.AlgebraicGeometry
