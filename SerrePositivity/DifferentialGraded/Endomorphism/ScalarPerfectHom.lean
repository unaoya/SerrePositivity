module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomCone
public import SerrePositivity.DifferentialGraded.Endomorphism.ActualScalarEnd
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting

/-! # Perfect始域に対する実際の全次数Hom係数変更比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomComparisonLocus_finiteCellCode {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) :
    scalarModuleHomComparisonLocus φ D ((moduleToHomotopy A D).obj M) := by
  let P := scalarModuleHomComparisonLocus φ D
  let Q := moduleToHomotopy A D
  let : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  induction c with
  | zero => exact scalarModuleHomComparisonLocus_zero φ D
  | generator x hx => exact scalarModuleHomComparisonLocus_representable φ D x
  | shift s c ih =>
      exact P.prop_of_iso ((Q.commShiftIso s).app _).symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
      let e := Q.mapIso (moduleBiprodIso A D M N) ≪≫ Q.mapBiprod M N ≪≫
        biprod.isoProd (Q.obj M) (Q.obj N)
      exact P.prop_of_iso e.symm (P.prop_prod _ _ ihc ihd)
  | cone c d f ihc ihd =>
      intro T
      exact scalarModuleHom_cone φ D f T (ihc T) (ihd T)
  | iso c e ih => exact P.prop_of_iso (Q.mapIso e) ih

lemma scalarModuleHom_quasiIso_of_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) (T : ModuleCategory A D) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)) := by
  obtain ⟨c⟩ := hM
  exact scalarModuleHomComparisonLocus_finiteCellCode φ D c T

/-- 導来圏のperfect retractを、射影的始域のHom同値でH⁰のretractへ持ち上げる。 -/
lemma scalarModuleHom_quasiIso_of_perfect {S : Set D} {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfectOver A D S ((moduleToDerived A D).obj M))
    (T : ModuleCategory A D) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)) := by
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfectOver_iff A D S _).mp hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  apply scalarModuleHom_quasiIso_of_homotopyRetract φ D i r _ T
    (scalarModuleHom_quasiIso_of_finiteCell φ D hN T)
  apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
  rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
    Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]

/-- U13の実際のenhancementの全Homについての係数変更比較。 -/
lemma perfectScalarModuleHom_homQuasiIso (S : Set D) :
    HomQuasiIso ((ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
      (scalarModuleDGFunctor φ D)) := by
  intro M N
  change QuasiIso ((ScalarExtension.extension φ).map (𝟙 _) ≫ scalarModuleHom φ D M.val N.val)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact scalarModuleHom_quasiIso_of_perfect φ D M.property.1 M.property.2
    (ForgetEnrichment.of (Complex A) N.val)

/-- perfect指定対象のEnd比較は全Homの擬同型となる。 -/
lemma actualScalarEnd_homQuasiIso (S : Set D) (E : PerfectDGModuleOver A D S) :
    HomQuasiIso (actualScalarEnd φ D E.val) := by
  intro x y
  exact scalarModuleHom_quasiIso_of_perfect φ D E.property.1 E.property.2
    (ForgetEnrichment.of (Complex A) E.val)

end SerrePositivity.DifferentialGraded
