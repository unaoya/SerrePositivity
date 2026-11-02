module
public import SerrePositivity.InfinityCategories.Derived.ContractingElementCriterion
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Functor.HomIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgNerve_isZeroVertex_of_representable_derived_isZero (x : D)
    (hx : IsZero ((moduleToDerived R D).obj
      (ForgetEnrichment.of (Complex R) (representable R x)))) :
    IsZeroVertex (X := dgNerve R D) (Simplex.vertex x) := by
  let X := ForgetEnrichment.of (Complex R) x
  let Y := dgYoneda R D
  let M := Y.onClosed.obj X
  let := Y.onHomotopy_faithful_of_homIso (fun a b => by
    change IsIso (dgYonedaIso R a (representable R b)).inv
    infer_instance)
  have hm : (moduleToHomotopy R D).map (𝟙 M) =
      (moduleToHomotopy R D).map (0 : M ⟶ M) := by
    apply (moduleProjectiveDerivedHomEquiv R D (representable_homotopicallyProjective R D x)
      M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 hx
  have hy : Y.onHomotopy.map ((toHomotopy R D).map (𝟙 X)) =
      Y.onHomotopy.map ((toHomotopy R D).map (0 : X ⟶ X)) := by
    change (moduleToHomotopy R D).map (Y.onClosed.map (𝟙 X)) =
      (moduleToHomotopy R D).map (Y.onClosed.map (0 : X ⟶ X))
    simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] using hm
  have h := Y.onHomotopy.map_injective hy
  obtain ⟨a, da⟩ := (toHomotopy_map_eq_iff_boundary R D (𝟙 X) (0 : X ⟶ X)).1 h
  apply dgNerve_contractingElement_isZeroVertex x a
  change (homObject R D x x).d (-1) 0 a = (unitElement R x).val - 0 at da
  simpa only [sub_zero] using da

lemma dgNerve_isZeroVertex_iff_representable_derived_isZero (x : D) :
    IsZeroVertex (X := dgNerve R D) (Simplex.vertex x) ↔
      IsZero ((moduleToDerived R D).obj
        (ForgetEnrichment.of (Complex R) (representable R x))) := by
  constructor
  · intro h
    obtain ⟨a, da⟩ := (dgNerve_isZeroVertex_iff_contractingElement x).1 h
    exact DGQuotient.representable_derived_isZero_of_unit_boundary R D x a da
  · exact dgNerve_isZeroVertex_of_representable_derived_isZero R D x

end SerrePositivity.InfinityCategories
