module

public import SerrePositivity.AlgebraicGeometry.CechRingIntegerCoefficients
public import SerrePositivity.AlgebraicGeometry.AffineGammaCechNaturality
public import SerrePositivity.AlgebraicGeometry.AffineGammaFrobeniusCechExact
public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram

/-!
概要：元のアフィンnerveのΓの増大Frobenius係数の完全性。
方針：既存の環のconerveとの自然同型と、B1の忠実平坦な場合の完全性を使う。
規約：同じ基底への射のΓと実際の係数環を保持する。
使われ方：同じ矩形の行へ平坦なアフィン射の完全性を供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]
variable (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
variable (hN : ∀ n : SimplexCategory,
  (p : (((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).obj n)) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の環のconerveから幾何的nerveのΓへの、同じFrobenius係数の自然同型。 -/
def affineGammaPerfectCoefficientIso :
    frobeniusRingDiagram (Arrow.mk (Scheme.Γ.map f.op)).cechConerve p hp
      (frobeniusConerve_primeCast (Arrow.mk (Scheme.Γ.map f.op)) p hS) ≅
        frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp hN :=
  frobeniusRingDiagramIso p hp
    (frobeniusConerve_primeCast (Arrow.mk (Scheme.Γ.map f.op)) p hS)
    (hE := hN) (affineGammaCechConerveIso f)

/-- 同じ基底の係数を保ち、元の幾何的nerveのΓへ移した増大係数。 -/
def affineGammaPerfectAugmentedCoefficients : CosimplicialObject.Augmented (ModuleCat.{u} ℤ) where
  left := ModuleCat.of ℤ (FrobeniusDirectLimit Γ(S, ⊤) p hp hS)
  right := frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp hN
  hom := ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj
    (frobeniusAugmentedRingCoefficients (Arrow.mk (Scheme.Γ.map f.op)) p hp hS)).hom ≫
      (affineGammaPerfectCoefficientIso f p hp hS hN).hom

set_option backward.isDefEq.respectTransparency false in
/-- 元の環の増大係数との、基底で恒等の同じ標準同型。 -/
def affineGammaPerfectAugmentedCoefficientsIso :
    ((CosimplicialObject.Augmented.whiskeringObj _ _ ringToCechIntegerModule).obj
      (frobeniusAugmentedRingCoefficients (Arrow.mk (Scheme.Γ.map f.op)) p hp hS)) ≅
        affineGammaPerfectAugmentedCoefficients f p hp hS hN :=
  Comma.isoMk (Iso.refl _) (affineGammaPerfectCoefficientIso f p hp hS hN) (by
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- 各増大成分は、元の幾何的nerveの基底への射のΓのFrobenius順極限。 -/
theorem affineGammaPerfectAugmentedCoefficients_hom_app_apply (n : SimplexCategory)
    (z : FrobeniusDirectLimit Γ(S, ⊤) p hp hS) :
    (((affineGammaPerfectAugmentedCoefficients f p hp hS hN).hom.app n).hom z) =
      frobeniusDirectLimitMap p hp hS (hN n)
        (Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op n)).op).hom z := by
  change frobeniusDirectLimitMap p hp _ (hN n)
    ((affineGammaCechConerveIso f).hom.app n).hom
    (frobeniusDirectLimitMap p hp hS _
      ((Arrow.mk (Scheme.Γ.map f.op)).augmentedCechConerve.hom.app n).hom z) = _
  have h := congrArg (fun m ↦ m z) (frobeniusDirectLimitMap_comp p hp hS
    (frobeniusConerve_primeCast (Arrow.mk (Scheme.Γ.map f.op)) p hS n)
    ((Arrow.mk (Scheme.Γ.map f.op)).augmentedCechConerve.hom.app n).hom
    (hN n) ((affineGammaCechConerveIso f).hom.app n).hom)
  have he := congrArg (fun m ↦ m.hom) (affineGammaCechConerveIso_augmentation f n)
  rw [CommRingCat.hom_comp] at he
  rw [he] at h
  exact h

/-- 元のアフィン間の平坦全射は、同じ幾何的nerveのΓの増大係数を完全にする。 -/
theorem affineGammaPerfectAugmentedCoefficients_acyclic [Flat f] [Surjective f] :
    (SerrePositivity.Cech.augmentedCochain.obj
      (affineGammaPerfectAugmentedCoefficients f p hp hS hN)).Acyclic := by
  have h := (ringCechExact_iff_integer_acyclic _).mp
    (affineGammaFrobeniusCech_exact_of_flat_surjective f p hp hS)
  intro n
  exact (h n).of_iso (SerrePositivity.Cech.augmentedCochain.mapIso
    (affineGammaPerfectAugmentedCoefficientsIso f p hp hS hN))

end SerrePositivity.AlgebraicGeometry
