module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveRingNaturality

/-!
概要：同じ conerve の実際の環の順極限を、元の矢印の図式の余極限と自然に比較する。
方針：既存の環の標準比較と、恒等成分の図式の比較を合成し、同じ有限段の脚で照合する。
規約：conerve の全ての次数の射と標準写像を保持する。
使われ方：実際の Frobenius 係数と、conerve の余極限保存への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

/-- 同じ conerve の各環の実際の順極限と、元の矢印の図式の同じ次数の余極限の標準同型。 -/
def frobeniusConerveRingColimitIso (n : SimplexCategory) :
    CommRingCat.of (FrobeniusDirectLimit (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) ≅
      colimit (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{u}).obj n) :=
  ringDirectLimitColimitIso (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
    (frobeniusConerve_primeCast f p hA n)) ≪≫
      colim.mapIso (frobeniusConerveRingDiagramIso f p hp hA hB n)

set_option backward.isDefEq.respectTransparency false in
/-- 標準同型は、同じ各有限段の環からの脚を保持する。 -/
theorem frobeniusConerveRingColimitIso_ι (n : SimplexCategory) (i : ℕ) :
    CommRingCat.ofHom (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i) ≫
      (frobeniusConerveRingColimitIso f p hp hA hB n).hom =
        colimit.ι (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
          (evaluation SimplexCategory CommRingCat.{u}).obj n) i := by
  change CommRingCat.ofHom (DirectLimit.Ring.of _
      (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n)) i) ≫
    ((ringDirectLimitColimitIso _).hom ≫
      colim.map (frobeniusConerveRingDiagramIso f p hp hA hB n).hom) = _
  rw [← Category.assoc, ringDirectLimitColimitIso_ι, colimit.ι_map,
    frobeniusConerveRingDiagramIso_hom_app]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限段の元を、元の矢印の図式の同じ標準脚へ送る公式。 -/
theorem frobeniusConerveRingColimitIso_of (n : SimplexCategory) (i : ℕ)
    (x : f.cechConerve.obj n) :
    (frobeniusConerveRingColimitIso f p hp hA hB n).hom.hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x) =
      (colimit.ι (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{u}).obj n) i).hom x :=
  congrArg (fun k : f.cechConerve.obj n ⟶ _ ↦ k.hom x)
    (frobeniusConerveRingColimitIso_ι f p hp hA hB n i)

set_option backward.isDefEq.respectTransparency false in
/-- 実際の環の順極限と同じ余極限の標準比較は、conerve の全ての次数の射に自然。 -/
theorem frobeniusConerveRingColimitIso_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    CommRingCat.ofHom (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
        (f.cechConerve.map a).hom) ≫
      (frobeniusConerveRingColimitIso f p hp hA hB m).hom =
    (frobeniusConerveRingColimitIso f p hp hA hB n).hom ≫
      colim.map (Functor.whiskerLeft
        (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve)
        ((evaluation SimplexCategory CommRingCat.{u}).map a)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) z
  change (frobeniusConerveRingColimitIso f p hp hA hB m).hom.hom
      (frobeniusDirectLimitMap p hp
        (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
        (f.cechConerve.map a).hom
        (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i x)) =
    (colim.map (Functor.whiskerLeft
      (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve)
      ((evaluation SimplexCategory CommRingCat.{u}).map a))).hom
        ((frobeniusConerveRingColimitIso f p hp hA hB n).hom.hom
          (frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
            (frobeniusConerve_primeCast f p hA n) i x))
  rw [frobeniusDirectLimitMap_of, frobeniusConerveRingColimitIso_of,
    frobeniusConerveRingColimitIso_of]
  exact (congrArg (fun k ↦ k.hom x) (colimit.ι_map (Functor.whiskerLeft
    (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve)
    ((evaluation SimplexCategory CommRingCat.{u}).map a)) i)).symm

end SerrePositivity.AlgebraicGeometry
