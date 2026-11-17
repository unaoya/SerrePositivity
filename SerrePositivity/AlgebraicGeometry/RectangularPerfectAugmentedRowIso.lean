module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectAugmentedRow
public import SerrePositivity.AlgebraicGeometry.AffineGammaPerfectAugmentedCoefficients
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowAugmentation
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowFunctorEvaluation
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectAugmentedRowAugmentation

/-!
概要：同じ有限交叉族のΓの増大係数と、元の矩形の増大行を比較する。
方針：元の行の標準同型とΓ–Specの基底の比較で増大を照合する。
規約：同じ実際のappLEとタプル被覆・基底の係数を保持する。
使われ方：平坦な有限アフィン族の完全性を元の増大行へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (k : ℕ)
variable (hS : (p : Γ(Spec (CommRingCat.of R), ⊤)) = 0)
variable (hN : ∀ n : SimplexCategory, (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0)
variable [IsAffine (∐ (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).toScheme))]

/-- 元の幾何的nerveのΓの増大係数と、同じ矩形の増大行との標準同型。 -/
def rectangularPerfectAugmentedRowIso :
    affineGammaPerfectAugmentedCoefficients
        (Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f)) p hp hS hN ≅
      rectangularPerfectAugmentedRow f U p hp hR k := by
  let e := frobeniusDirectLimitRingIso p hp hS hR (Scheme.ΓSpecIso (CommRingCat.of R))
  let e0 :
      (affineGammaPerfectAugmentedCoefficients
        (Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f)) p hp hS hN).left ≅
      (rectangularPerfectAugmentedRow f U p hp hR k).left :=
    (e.toAddEquiv.toIntLinearEquiv
      (modM := (affineGammaPerfectAugmentedCoefficients
        (Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f)) p hp hS hN).left.isModule)
      (modM₂ := (rectangularPerfectAugmentedRow f U p hp hR k).left.isModule)).toModuleIso
  let en := rectangularPerfectRowFunctorIso f U p hp
    (schemeCechNervePresheaf_primeCast f p hR) k hN
  refine Comma.isoMk e0 en ?_
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext q
  simp only [NatTrans.comp_app, Functor.const_map_app, Functor.id_map,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  have h0 : e0.hom.hom z = frobeniusDirectLimitMap p hp hS hR
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z := rfl
  have heval (a : (frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k)
      p hp hN).obj n) :
      ((en.hom.app n).hom a) q = rectangularPerfectRowEquiv f U p hp n k (hN n)
        (fun q ↦ schemeCechNervePresheaf_primeCast f p hR (op n)
          (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))))
        a q :=
    rectangularPerfectRowFunctorIso_hom_apply f U p hp
      (schemeCechNervePresheaf_primeCast f p hR) k hN n a q
  have hw := rectangularPerfectAugmentedRow_augmentation f U p hp hR k hS hN n z q
  have hg := affineGammaPerfectAugmentedCoefficients_hom_app_apply
    (Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f)) p hp hS hN n z
  have hleft := congrArg (fun x ↦
    (((rectangularPerfectAugmentedRow f U p hp hR k).hom.app n).hom x) q) h0
  have hmid := congrArg (fun x ↦ rectangularPerfectRowEquiv f U p hp n k (hN n)
    (fun q ↦ schemeCechNervePresheaf_primeCast f p hR (op n)
      (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))))
    x q) hg
  exact hleft.trans (hw.trans (hmid.symm.trans (heval
    (((affineGammaPerfectAugmentedCoefficients
      (Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))
        p hp hS hN).hom.app n).hom z)).symm))

end SerrePositivity.AlgebraicGeometry
