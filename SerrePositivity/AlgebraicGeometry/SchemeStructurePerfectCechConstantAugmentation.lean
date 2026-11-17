module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechConstantComplexAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechAugmentation

/-!
概要：元の構造層のFrobenius係数に全次数の定数増大を代入する。
方針：同じ大域スカラーをFrobenius順極限に送り、元の開への制限を合成する。
規約：同じsingleからの増大と各タプルでの実際の切断を保持する。
使われ方：元のタプル被覆の二重Čechで行の完全性を供給する入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) (φ : R →+* Γ(Y, ⊤))
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι : Type} [LinearOrder ι] (U : ι → Y.Opens)

/-- 元の大域スカラーと同じ開への制限を使う、全次数の定数増大。 -/
def schemeStructurePerfectCechConstantAugmentation :
    cechConstantComplex (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ⟶
      fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) :=
  openCoverCechConstantComplexAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U
    (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
    (ModuleCat.ofHom (frobeniusDirectLimitMap p hp hR (hY (op ⊤)) φ).toAddMonoidHom.toIntLinearMap)

set_option backward.isDefEq.respectTransparency false in
/-- 各タプルで元のスカラーと実際の交叉への制限の合成を取る。 -/
theorem schemeStructurePerfectCechConstantAugmentation_apply (q : ℕ)
    (x : FrobeniusDirectLimit R p hp hR) (t : Fin (q + 1) → ι) :
    ((schemeStructurePerfectCechConstantAugmentation Y φ p hp hR hY U).f q).hom x t =
      frobeniusDirectLimitMap p hp hR (hY (op (cechOpenIntersection U (cechTupleSupport t))))
        ((Y.presheaf.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤
          from le_top)).op).hom.comp φ) x := by
  rw [schemeStructurePerfectCechConstantAugmentation,
    openCoverCechConstantComplexAugmentation_apply]
  exact congrArg (fun z ↦ z x) (frobeniusDirectLimitMap_comp p hp hR (hY (op ⊤)) φ
    (hY (op (cechOpenIntersection U (cechTupleSupport t))))
    (Y.presheaf.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤
      from le_top)).op).hom)

set_option backward.isDefEq.respectTransparency false in
/-- 元のsingleからの包含との合成の零次は、既存の同じ増大写像。 -/
theorem schemeStructurePerfectCechConstantAugmentation_single_zero :
    (cechConstantSingleAugmentation (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) ≫
      schemeStructurePerfectCechConstantAugmentation Y φ p hp hR hY U).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫
        ModuleCat.ofHom (schemeStructurePerfectCechAugmentation Y φ p hp hR hY U) := by
  rw [HomologicalComplex.comp_f, cechConstantSingleAugmentation_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext t
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [schemeStructurePerfectCechConstantAugmentation_apply,
    schemeStructurePerfectCechAugmentation_apply]
  rfl

end SerrePositivity.AlgebraicGeometry
