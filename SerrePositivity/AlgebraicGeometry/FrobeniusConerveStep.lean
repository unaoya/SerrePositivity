module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowDiagramMaps

/-!
概要：元の矢印の Frobenius が誘導する conerve の射を、同じ環の Frobenius と照合する。
方針：同じ有限余積の head と全ての脚で普遍性を使う。
規約：余積の環・元の脚・標数の写像を保持し、零環を許す。
使われ方：同じ conerve の反復図式と係数の Frobenius 系との比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

include hA in
/-- 同じ conerve の環で p が零であることは、元の基底からの実際の head が与える。 -/
theorem frobeniusConerve_primeCast (n : SimplexCategory) :
    (p : f.cechConerve.obj n) = 0 := by
  let k : f.left ⟶ f.cechConerve.obj n := WidePushout.head _
  rw [← map_natCast k.hom p, hA, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- 元の Frobenius の四角形が誘導する各 conerve の射は、同じ環の Frobenius。 -/
theorem frobeniusConerve_step (n : SimplexCategory) :
    (Arrow.mapCechConerve (frobeniusArrowStep f p hp hA hB)).app n =
      CommRingCat.ofHom (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) 0 1 (by decide)) := by
  apply WidePushout.hom_ext
  · intro i
    rw [Arrow.mapCechConerve_app, WidePushout.ι_desc]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (WidePushout.ι (fun _ : Fin (n.len + 1) ↦ f.hom) i).hom
        (frobeniusDirectSystemMap f.right p hp hB 0 1 (by decide) x) =
      frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) 0 1 (by decide)
          ((WidePushout.ι (fun _ : Fin (n.len + 1) ↦ f.hom) i).hom x)
    exact frobeniusDirectSystemMap_naturality p hp hB
      (frobeniusConerve_primeCast f p hA n)
      (WidePushout.ι (fun _ : Fin (n.len + 1) ↦ f.hom) i).hom 0 1 (by decide) x
  · rw [Arrow.mapCechConerve_app, WidePushout.head_desc]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (WidePushout.head (fun _ : Fin (n.len + 1) ↦ f.hom)).hom
        (frobeniusDirectSystemMap f.left p hp hA 0 1 (by decide) x) =
      frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) 0 1 (by decide)
          ((WidePushout.head (fun _ : Fin (n.len + 1) ↦ f.hom)).hom x)
    exact frobeniusDirectSystemMap_naturality p hp hA
      (frobeniusConerve_primeCast f p hA n)
      (WidePushout.head (fun _ : Fin (n.len + 1) ↦ f.hom)).hom 0 1 (by decide) x

end SerrePositivity.AlgebraicGeometry
