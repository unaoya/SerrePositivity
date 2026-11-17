module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConervePerfectIso

/-!
概要：実際の Frobenius の conerve の標準比較は、次数の射と増大写像を保持する。
方針：同じ有限段の標準脚で、元の conerve の自然性と増大の可換性を評価する。
規約：各環の同型を独立に選ばず、検証した同じ標準比較を使う。
使われ方：Frobenius の係数とアフィン conerve の増大図式の自然な比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の標準比較は、元の conerve の全ての次数の射に自然。 -/
theorem frobeniusConervePerfectIso_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    CommRingCat.ofHom (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
        (f.cechConerve.map a).hom) ≫
      (frobeniusConervePerfectIso f p hp hA hB m).hom =
    (frobeniusConervePerfectIso f p hp hA hB n).hom ≫
      (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).cechConerve.map a := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) z
  change (frobeniusConervePerfectIso f p hp hA hB m).hom.hom
      (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
        (f.cechConerve.map a).hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x)) =
    ((Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).cechConerve.map a).hom
        ((frobeniusConervePerfectIso f p hp hA hB n).hom.hom
          (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
            (frobeniusConerve_primeCast f p hA n) i x))
  rw [frobeniusDirectLimitMap_of, frobeniusConervePerfectIso_of, frobeniusConervePerfectIso_of]
  exact congrArg (fun k ↦ k.hom x)
    ((Arrow.mapCechConerve ((frobeniusArrowCocone f p hp hA hB).ι.app i)).naturality a)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準比較は、元の基底環の Frobenius 順極限からの実際の増大写像を保つ。 -/
theorem frobeniusConervePerfectIso_augmentation (n : SimplexCategory) :
    CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA
        (frobeniusConerve_primeCast f p hA n) (f.augmentedCechConerve.hom.app n).hom) ≫
      (frobeniusConervePerfectIso f p hp hA hB n).hom =
    (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve.hom.app n := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap f.left p hp hA) z
  change (frobeniusConervePerfectIso f p hp hA hB n).hom.hom
      (frobeniusDirectLimitMap p hp hA (frobeniusConerve_primeCast f p hA n)
        (f.augmentedCechConerve.hom.app n).hom (frobeniusDirectLimitOf f.left p hp hA i x)) =
    ((Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve.hom.app n).hom
        (frobeniusDirectLimitOf f.left p hp hA i x)
  rw [frobeniusDirectLimitMap_of, frobeniusConervePerfectIso_of]
  exact (congrArg (fun k ↦ k.hom x) (CosimplicialObject.Augmented.w_app
    (η := Arrow.mapAugmentedCechConerve ((frobeniusArrowCocone f p hp hA hB).ι.app i))
    (n := n))).symm

end SerrePositivity.AlgebraicGeometry
