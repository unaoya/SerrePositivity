module
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomology
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Derived.Evaluation

/-! # 代表加群からの導来射と評価先の次数零ホモロジー -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全Hom endの次数零ホモロジーによる射影的始域の射計算。 -/
def moduleProjectiveDerivedHomologyEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) ≃
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)).homology 0 :=
  (moduleProjectiveDerivedHomEquiv A D hP N).symm.trans
    (homotopyHomologyEquiv A (RightModule A D) P N)

lemma moduleProjectiveDerivedHomologyEquiv_map {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (f : P ⟶ N) :
    moduleProjectiveDerivedHomologyEquiv A D hP N ((moduleToDerived A D).map f) =
      complexZeroHomologyClass A (homObject A (RightModule A D) P N)
        (closedHomEquiv A (RightModule A D) P N f) := by
  rw [← moduleProjectiveDerivedHomEquiv_map A D hP f]
  change homotopyHomologyEquiv A (RightModule A D) P N
    ((moduleProjectiveDerivedHomEquiv A D hP N).symm
      ((moduleProjectiveDerivedHomEquiv A D hP N) ((moduleToHomotopy A D).map f))) = _
  rw [Equiv.symm_apply_apply]
  exact homotopyHomologyEquiv_map A (RightModule A D) P N f

/-- dg Yonedaと実際の局所化Hom計算の合成。Hom_Dのflat性は不要。 -/
def moduleRepresentableDerivedHomologyEquiv (x : D) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) ≃
        ((ForgetEnrichment.to (Complex A) N).obj (op x)).homology 0 :=
  (moduleProjectiveDerivedHomologyEquiv A D (representable_homotopicallyProjective A D x) N).trans
    (HomologicalComplex.homologyMapIso
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)) 0).toLinearEquiv.toEquiv

lemma moduleRepresentableDerivedHomologyEquiv_map (x : D) {N : ModuleCategory A D}
    (f : ForgetEnrichment.of (Complex A) (representable A x) ⟶ N) :
    moduleRepresentableDerivedHomologyEquiv A D x N ((moduleToDerived A D).map f) =
      homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
        (complexZeroHomologyClass A
          (moduleHom A D (representable A x) (ForgetEnrichment.to (Complex A) N))
          (closedHomEquiv A (RightModule A D)
            (ForgetEnrichment.of (Complex A) (representable A x)) N f)) := by
  change homologyMap (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)).hom 0
    (moduleProjectiveDerivedHomologyEquiv A D
      (representable_homotopicallyProjective A D x) N ((moduleToDerived A D).map f)) = _
  rw [moduleProjectiveDerivedHomologyEquiv_map]
  rfl

/-- 任意の主導来対象についての代表加群による評価ホモロジーの表示。 -/
def moduleRepresentableDerivedHomEquiv (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃
      (moduleDerivedHomology A D x 0).obj X := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableDerivedHomologyEquiv A D x N

lemma moduleRepresentableDerivedHomEquiv_obj (x : D) (N : ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    moduleRepresentableDerivedHomEquiv A D x ((moduleToDerived A D).obj N) f =
      moduleRepresentableDerivedHomologyEquiv A D x N f := rfl

end SerrePositivity.DifferentialGraded
