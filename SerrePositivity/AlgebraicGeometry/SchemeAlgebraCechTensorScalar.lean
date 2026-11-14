module

public import SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorDifferential

/-!
概要：切断部分代数の flat 底変換比較は、基底環のスカラー写像と可換。
方針：実際の切断の引き戻しは 1 を保ち、残りは A 線形性から得る。
規約：a ⊗ 1 の像は実際の algebraMap の値。
使われ方：中心外の同型から元の余核の局所化の消滅へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct
open scoped TensorProduct ChangeOfRings
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [DecidableEq ι] [Fintype ι] (U : ι → X.Opens)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))


omit [Fintype ι] [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- 実際の底変換の切断の引き戻しは 1 を保つ。 -/
theorem schemeStructureCechBaseChangeDiagramRestriction_one (T : Finset ι) :
    ((schemeStructureCechBaseChangeDiagramRestriction (algebraMap R A) iX iY g H.w U).app T).hom
      (1 : Γ(X, cechOpenIntersection U T)) =
      (1 : Γ(Y, cechOpenIntersection (fun i ↦ g ⁻¹ᵁ U i) T)) := by
  change (Y.presheaf.map _).hom ((g.app _).hom 1) = 1
  rw [map_one, map_one]

/-- 実際の flat な切断部分代数の比較は 1 ⊗ 1 を 1 に送る。 -/
theorem schemeAlgebraCechTensorEquiv_one [Module.Flat R A] :
    schemeAlgebraCechTensorEquiv iX iY g H U hU ((1 : A) ⊗ₜ[R] 1) = 1 := by
  apply Subtype.ext
  funext t
  change (((schemeStructureCechNativeTensorComplexIso iX iY g H U hU).hom.f 0).hom
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app _
      (fun t ↦ (1 : Γ(X, cechOpenIntersection U (cechTupleSupport t)))))) t =
      (1 : Γ(Y, cechOpenIntersection (fun i ↦ g ⁻¹ᵁ U i) (cechTupleSupport t)))
  exact (schemeStructureCechNativeTensorComplexIso_unit_apply iX iY g H U hU 0 _ t).trans
    (schemeStructureCechBaseChangeDiagramRestriction_one iX iY g H U (cechTupleSupport t))

/-- 実際の flat な切断部分代数の比較は基底環のスカラー写像と可換。 -/
theorem schemeAlgebraCechTensorEquiv_scalar [Module.Flat R A] (a : A) :
    schemeAlgebraCechTensorEquiv iX iY g H U hU (a ⊗ₜ[R] 1) =
      algebraMap A (fullAlgebraCechEqualizer
        (schemeSectionAlgebraCechDiagram Y (schemeScalarHom Y iY) (fun i ↦ g ⁻¹ᵁ U i))) a := by
  have ht : a ⊗ₜ[R] (1 : fullAlgebraCechEqualizer
      (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U)) =
      a • ((1 : A) ⊗ₜ[R] 1) := by
    rw [TensorProduct.smul_tmul']
    simp only [smul_eq_mul, mul_one]
  rw [ht, map_smul, schemeAlgebraCechTensorEquiv_one, Algebra.smul_def, mul_one]

end SerrePositivity.AlgebraicGeometry
