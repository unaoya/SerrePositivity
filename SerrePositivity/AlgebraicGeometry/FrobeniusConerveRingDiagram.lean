module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveStep

/-!
概要：同じ conerve の各環の Frobenius 系を、元の矢印の反復図式と比較する。
方針：恒等成分の自然性を後続射で示し、既存の ofSequence の普遍性で全ての段へ渡す。
規約：同じ有限余積の環と元の全ての射を保持する。
使われ方：conerve の余極限保存と実際の係数環の順極限を結ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ conerve の各環の Frobenius 系と、元の矢印の反復図式の同じ次数の標準比較。
各段の成分は恒等であり、元の有限余積の環を変えない。 -/
def frobeniusConerveRingDiagramIso (n : SimplexCategory) :
    ringDirectSystemFunctor (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) ≅
      frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{u}).obj n := by
  let t : ringDirectSystemFunctor (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) ⟶
      frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{u}).obj n :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 (f.cechConerve.obj n)) (by
      intro i
      change CommRingCat.ofHom (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i (i + 1) (i.le_add_right 1)) ≫ 𝟙 _ =
        𝟙 _ ≫ (Arrow.mapCechConerve
          ((Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep f p hp hA hB)).map
            (homOfLE (i.le_add_right 1)))).app n
      rw [Functor.ofSequence_map_homOfLE_succ]
      change CommRingCat.ofHom (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i (i + 1) (i.le_add_right 1)) ≫
            𝟙 (f.cechConerve.obj n) = 𝟙 (f.cechConerve.obj n) ≫
              (Arrow.mapCechConerve (frobeniusArrowStep f p hp hA hB)).app n
      rw [frobeniusConerve_step]
      simp only [Category.comp_id, Category.id_comp]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) i (i + 1) (i.le_add_right 1) x =
        frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
          (frobeniusConerve_primeCast f p hA n) 0 1 (by decide) x
      rw [frobeniusDirectSystemMap_apply, frobeniusDirectSystemMap_apply]
      simp)
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun a ↦ t.naturality a)

/-- 任意の有限段の比較成分は、元の環の恒等射。 -/
theorem frobeniusConerveRingDiagramIso_hom_app (n : SimplexCategory) (i : ℕ) :
    (frobeniusConerveRingDiagramIso f p hp hA hB n).hom.app i =
      𝟙 (f.cechConerve.obj n) := rfl

end SerrePositivity.AlgebraicGeometry
