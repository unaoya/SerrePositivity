module

public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitIntNaturality
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：環の前層の Frobenius 順極限を、整数加群の図式の順極限として表示する。
方針：各交叉の環の既存の順極限比較を自然同型にまとめる。
規約：段の遷移も交叉の制限も、実際の環準同型の加法部分を使う。
使われ方：共通アフィン細分の同型性を Frobenius 後へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {J : Type w} [Category.{v} J]
variable (D : J ⥤ CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hD : ∀ T, (p : D.obj T) = 0)

/-- 各対象の環の Frobenius 系と、制限の実際の環準同型。 -/
def frobeniusRingObjectSystem : J ⥤ ℕ ⥤ ModuleCat.{u} ℤ where
  obj T := linearDirectSystemFunctor
    (ringDirectSystemIntMap (frobeniusDirectSystemMap (D.obj T) p hp (hD T)))
  map {T U} f := frobeniusIntDirectSystemNatTrans p hp (hD T) (hD U) (D.map f).hom
  map_id T := by
    ext n x
    change (D.map (𝟙 T)).hom x = x
    rw [D.map_id]
    rfl
  map_comp {T U V} f g := by
    ext n x
    change (D.map (f ≫ g)).hom x = (D.map g).hom ((D.map f).hom x)
    rw [D.map_comp]
    rfl

/-- 同じ系を、Frobenius の各段を外側の添字とする図式にする。 -/
def frobeniusRingSequentialDiagram : ℕ ⥤ J ⥤ ModuleCat.{u} ℤ :=
  (frobeniusRingObjectSystem D p hp hD).flip

/-- 各環の順極限との比較は、環の図式の制限に自然。 -/
def frobeniusRingObjectColimitIso :
    frobeniusRingObjectSystem D p hp hD ⋙ colim ≅ frobeniusRingDiagram D p hp hD :=
  NatIso.ofComponents
    (fun T ↦ (ringDirectLimitIntColimitIso
      (frobeniusDirectSystemMap (D.obj T) p hp (hD T))).symm) (by
        intro T U f
        let eT := ringDirectLimitIntColimitIso
          (frobeniusDirectSystemMap (D.obj T) p hp (hD T))
        let eU := ringDirectLimitIntColimitIso
          (frobeniusDirectSystemMap (D.obj U) p hp (hD U))
        change colim.map (frobeniusIntDirectSystemNatTrans p hp (hD T) (hD U)
          (D.map f).hom) ≫ eU.inv = eT.inv ≫ _
        apply (cancel_epi eT.hom).mp
        rw [← Category.assoc, ← frobeniusDirectLimitIntColimitIso_naturality]
        simp only [eU, Category.assoc, Iso.hom_inv_id, Category.comp_id,
          Iso.hom_inv_id_assoc]
        rfl)

/-- 図式の順極限は、同じ各環の実際の Frobenius 順極限を係数に持つ図式。 -/
def frobeniusRingSequentialColimitIso :
    colimit (frobeniusRingSequentialDiagram D p hp hD) ≅
      frobeniusRingDiagram D p hp hD :=
  colimitFlipIsoCompColim (frobeniusRingObjectSystem D p hp hD) ≪≫
    frobeniusRingObjectColimitIso D p hp hD

end SerrePositivity.AlgebraicGeometry
