module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedTria
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：元の dg nerve の h 圏と tria の同じ代表対象の間で retract を移す。
方針：Yoneda を有限 cell のホモトピー圏へ制限し、主導来比較の完全忠実性を使う。
規約：射影性のない対象間で導来射を持ち上げず、代表対象の比較に限定する。
使われ方：D-16 追加 (3) の thick 核と実安定閉包の retract 表示の橋。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

def dgH0FiniteCellYoneda :
    _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R D ⥤ _root_.SerrePositivity.DifferentialGraded.HomotopyFiniteCellCategoryOver R D Set.univ :=
  (_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver R D Set.univ).lift (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).onHomotopy (by
    intro X
    obtain ⟨x⟩ := X
    exact (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver R D Set.univ).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D)
      (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCell_representable R D x))

def dgH0FiniteCellYonedaFullyFaithful : (dgH0FiniteCellYoneda R D).FullyFaithful := by
  let Y := _root_.SerrePositivity.DifferentialGraded.dgYoneda R D
  let := Y.onHomotopy_full_of_homIso (fun a b => by
    change IsIso (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R a (_root_.SerrePositivity.DifferentialGraded.representable R b)).inv
    infer_instance)
  let := Y.onHomotopy_faithful_of_homIso (fun a b => by
    change IsIso (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R a (_root_.SerrePositivity.DifferentialGraded.representable R b)).inv
    infer_instance)
  let h := CategoryTheory.Functor.FullyFaithful.ofFullyFaithful Y.onHomotopy
  exact {
    preimage f := h.preimage f.hom
    map_preimage f := (_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver R D Set.univ).hom_ext (h.map_preimage f.hom)
    preimage_map f := h.preimage_map f }

def dgNativeTriaFunctor :
    SSet.hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⥤ TriaCategory R D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R D).functor ⋙ dgH0FiniteCellYoneda R D ⋙
    _root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellToTria R D Set.univ

def dgNativeTriaFunctorFullyFaithful : (dgNativeTriaFunctor R D).FullyFaithful :=
  (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R D).functor).comp
    ((dgH0FiniteCellYonedaFullyFaithful R D).comp
      (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful
        (_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellToTria R D Set.univ)))

def dgNativeTriaFunctorRepresentableIso (x : D) :
    (dgNativeTriaFunctor R D).obj (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) ≅
      triaRepresentable R D x :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyFiniteCellRepresentableTriaIso R D x

lemma dgNative_retract_iff_tria_retract (x y : D) :
    Nonempty (Retract (SSet.HomotopyCategory.mk (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (SSet.HomotopyCategory.mk (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) ↔
      Nonempty (Retract (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D x) (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D y)) := by
  let H := dgNativeTriaFunctor R D
  let hH := dgNativeTriaFunctorFullyFaithful R D
  let ex := dgNativeTriaFunctorRepresentableIso R D x
  let ey := dgNativeTriaFunctorRepresentableIso R D y
  constructor
  · rintro ⟨r⟩
    exact ⟨(Retract.ofIso ex.symm).trans ((r.map H).trans (Retract.ofIso ey))⟩
  · rintro ⟨r⟩
    let r' := (Retract.ofIso ex).trans (r.trans (Retract.ofIso ey.symm))
    refine ⟨{ i := hH.preimage r'.i, r := hH.preimage r'.r, retract := ?_ }⟩
    apply hH.map_injective
    rw [CategoryTheory.Functor.map_comp, hH.map_preimage, hH.map_preimage,
      r'.retract, CategoryTheory.Functor.map_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
