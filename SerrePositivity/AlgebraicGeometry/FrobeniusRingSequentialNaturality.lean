module

public import SerrePositivity.AlgebraicGeometry.FrobeniusRingSequentialDiagram

/-!
概要：実際の環の Frobenius 順極限の表示を、係数環の図式の射に自然にする。
方針：環の順極限の既存の自然性と、添字を交換する余極限比較の自然性を合成する。
規約：各段にも順極限にも同じ実際の環準同型を使う。
使われ方：底変換・閉厚化・R/J の係数表示と Frobenius 順極限の可換性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u v w
variable {J : Type w} [Category.{v} J]
variable {D E : J ⥤ CommRingCat.{u}} (p : ℕ) (hp : p.Prime)
variable (hD : ∀ T, (p : D.obj T) = 0) (hE : ∀ T, (p : E.obj T) = 0)

/-- 環の図式の射を、各対象の実際の Frobenius 系の射へ送る。 -/
def frobeniusRingObjectSystemMap (η : D ⟶ E) :
    frobeniusRingObjectSystem D p hp hD ⟶ frobeniusRingObjectSystem E p hp hE where
  app T := frobeniusIntDirectSystemNatTrans p hp (hD T) (hE T) (η.app T).hom
  naturality {T U} f := by
    ext n x
    exact congrArg (fun m ↦ m.hom x) (η.naturality f)

/-- 同じ環の図式の射を、Frobenius 段を外側にした図式の射へ送る。 -/
def frobeniusRingSequentialDiagramMap (η : D ⟶ E) :
    frobeniusRingSequentialDiagram D p hp hD ⟶ frobeniusRingSequentialDiagram E p hp hE :=
  (flipFunctor J ℕ (ModuleCat.{u} ℤ)).map (frobeniusRingObjectSystemMap p hp hD hE η)

/-- 各対象の環の順極限との比較は、実際の環の図式の射に自然。 -/
theorem frobeniusRingObjectColimitIso_naturality (η : D ⟶ E) :
    whiskerRight (frobeniusRingObjectSystemMap p hp hD hE η) colim ≫
        (frobeniusRingObjectColimitIso E p hp hE).hom =
      (frobeniusRingObjectColimitIso D p hp hD).hom ≫
        frobeniusRingDiagramMap p hp hD (hE := hE) η := by
  apply NatTrans.ext
  funext T
  change colim.map (frobeniusIntDirectSystemNatTrans p hp (hD T) (hE T) (η.app T).hom) ≫
      (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap (E.obj T) p hp (hE T))).inv =
    (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap (D.obj T) p hp (hD T))).inv ≫ _
  apply (cancel_epi
    (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap (D.obj T) p hp (hD T))).hom).mp
  rw [← Category.assoc, ← frobeniusDirectLimitIntColimitIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rfl

/-- 図式の順極限と実際の環の Frobenius 順極限の比較は、環の図式の射に自然。 -/
theorem frobeniusRingSequentialColimitIso_naturality (η : D ⟶ E) :
    colim.map (frobeniusRingSequentialDiagramMap p hp hD hE η) ≫
        (frobeniusRingSequentialColimitIso E p hp hE).hom =
      (frobeniusRingSequentialColimitIso D p hp hD).hom ≫
        frobeniusRingDiagramMap p hp hD (hE := hE) η := by
  dsimp only [frobeniusRingSequentialColimitIso, Iso.trans_hom,
    frobeniusRingSequentialDiagramMap, frobeniusRingSequentialDiagram]
  have h := (colimCompFlipIsoWhiskerColim (K := J) (J := ℕ)
    (C := ModuleCat.{u} ℤ)).hom.naturality (frobeniusRingObjectSystemMap p hp hD hE η)
  change colim.map ((flipFunctor J ℕ (ModuleCat.{u} ℤ)).map
      (frobeniusRingObjectSystemMap p hp hD hE η)) ≫
      (colimitFlipIsoCompColim (frobeniusRingObjectSystem E p hp hE)).hom =
    (colimitFlipIsoCompColim (frobeniusRingObjectSystem D p hp hD)).hom ≫
      whiskerRight (frobeniusRingObjectSystemMap p hp hD hE η) colim at h
  rw [← Category.assoc, h, Category.assoc, frobeniusRingObjectColimitIso_naturality]
  simp only [Category.assoc]

end SerrePositivity.AlgebraicGeometry
