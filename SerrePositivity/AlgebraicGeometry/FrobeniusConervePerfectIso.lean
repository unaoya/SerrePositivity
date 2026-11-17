module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveRingColimit
public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveCocone

/-!
概要：同じ conerve の環の実際の Frobenius 順極限を、実際の順極限の矢印の conerve へ渡す。
方針：同じ環の標準比較と、同じ矢印の余錐を conerve へ写した普遍性を合成する。
規約：各有限段の標準脚を保持する。
使われ方：元のアフィン Čech の Frobenius 係数と、実際の環の矢印の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

/-- 同じ conerve の係数環の実際の順極限と、実際の順極限の矢印の conerve の標準同型。 -/
def frobeniusConervePerfectIso (n : SimplexCategory) :
    CommRingCat.of (FrobeniusDirectLimit (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) ≅
      (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).cechConerve.obj n :=
  frobeniusConerveRingColimitIso f p hp hA hB n ≪≫
    ((frobeniusConerveIsColimit f p hp hA hB n).coconePointUniqueUpToIso
      (colimit.isColimit _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- 実際の順極限の比較は、元の矢印の各有限段の脚の conerve の射を保つ。 -/
theorem frobeniusConervePerfectIso_ι (n : SimplexCategory) (i : ℕ) :
    CommRingCat.ofHom (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i) ≫
      (frobeniusConervePerfectIso f p hp hA hB n).hom =
        (Arrow.mapCechConerve ((frobeniusArrowCocone f p hp hA hB).ι.app i)).app n := by
  change CommRingCat.ofHom (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n) i) ≫
    ((frobeniusConerveRingColimitIso f p hp hA hB n).hom ≫
      ((frobeniusConerveIsColimit f p hp hA hB n).coconePointUniqueUpToIso
        (colimit.isColimit _)).inv) = _
  rw [← Category.assoc, frobeniusConerveRingColimitIso_ι]
  exact (frobeniusConerveIsColimit f p hp hA hB n).comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit _) i

set_option backward.isDefEq.respectTransparency false in
/-- 実際の同型の有限段の評価も、元の矢印の同じ脚の conerve である。 -/
theorem frobeniusConervePerfectIso_of (n : SimplexCategory) (i : ℕ)
    (x : f.cechConerve.obj n) :
    (frobeniusConervePerfectIso f p hp hA hB n).hom.hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x) =
      ((Arrow.mapCechConerve ((frobeniusArrowCocone f p hp hA hB).ι.app i)).app n).hom x :=
  congrArg (fun k : f.cechConerve.obj n ⟶ _ ↦ k.hom x)
    (frobeniusConervePerfectIso_ι f p hp hA hB n i)

end SerrePositivity.AlgebraicGeometry
