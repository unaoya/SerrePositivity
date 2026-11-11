module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementCriterion
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：dg 対象の実零頂点性と、その代表加群の主導来圏での零性を同定する。
方針：代表加群の射影性で恒等と零の等式を戻し、全 Hom Yoneda の忠実性で収縮元を得る。
規約：前三角性を要求せず、Small は元の dg 圏にだけ課す。
使われ方：D-16 の平坦商の実零頂点判定を、既存の Verdier 核判定へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgNerve_isZeroVertex_of_representable_derived_isZero (x : D)
    (hx : IsZero ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R x)))) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  let X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x
  let Y := _root_.SerrePositivity.DifferentialGraded.dgYoneda R D
  let M := Y.onClosed.obj X
  let := Y.onHomotopy_faithful_of_homIso (fun a b => by
    change IsIso (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R a (_root_.SerrePositivity.DifferentialGraded.representable R b)).inv
    infer_instance)
  have hm : (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (𝟙 M) =
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (0 : M ⟶ M) := by
    apply (_root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv R D (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R D x)
      M).injective
    rw [_root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv_map, _root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv_map]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hx
  have hy : Y.onHomotopy.map ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R D).map (𝟙 X)) =
      Y.onHomotopy.map ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R D).map (0 : X ⟶ X)) := by
    change (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (Y.onClosed.map (𝟙 X)) =
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).map (Y.onClosed.map (0 : X ⟶ X))
    simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] using hm
  have h := Y.onHomotopy.map_injective hy
  obtain ⟨a, da⟩ := (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary R D (𝟙 X) (0 : X ⟶ X)).1 h
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex x a
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x x).d (-1) 0 a = (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val - 0 at da
  simpa only [sub_zero] using da

lemma dgNerve_isZeroVertex_iff_representable_derived_isZero (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) ↔
      IsZero ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R x))) := by
  constructor
  · intro h
    obtain ⟨a, da⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_contractingElement x).1 h
    exact _root_.SerrePositivity.DifferentialGraded.DGQuotient.representable_derived_isZero_of_unit_boundary R D x a da
  · exact dgNerve_isZeroVertex_of_representable_derived_isZero R D x

end SerrePositivity.InfinityCategories.Project.DerivedCategories
