module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedFiniteCells

/-! # 前三角性と tria の代表対象

概要：K(D) の前三角性は導来加群圏の tria の全対象が代表対象と同型であることと同値。
方針：有限 cell 上の主導来局所化の完全忠実性で同型を戻す。
規約：主導来圏の同型を無条件で K(D) の同型と扱わない。使われ方：平坦商の前三角性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表対象を含む K(D) の有限 cell 部分圏の対象。 -/
def dgHomotopyFiniteCellRepresentable (x : D) :
    HomotopyFiniteCellCategoryOver A D Set.univ :=
  ⟨(moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A x)),
    (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D x)⟩

/-- 有限 cell 比較関手は実代表対象を tria の同じ代表対象へ送る。 -/
def dgHomotopyFiniteCellRepresentableTriaIso (x : D) :
    (homotopyFiniteCellToTria A D Set.univ).obj (dgHomotopyFiniteCellRepresentable A D x) ≅
      triaRepresentable A D x :=
  (derivedFiniteCellOver A D Set.univ).isoMk
    ((moduleToHomotopyDerivedIso A D).app
      (ForgetEnrichment.of (Complex A) (representable A x)))

/-- tria の全対象が代表対象なら有限 cell の K(D) の全対象もホモトピー表現可能。 -/
lemma isDGPretriangulated_of_tria_representable
    (h : ∀ X : TriaCategory A D, ∃ x : D, Nonempty (X ≅ triaRepresentable A D x)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_iff_finiteCell_representable A D).2
  intro M hM
  let a : HomotopyFiniteCellCategoryOver A D Set.univ := ⟨M, hM⟩
  obtain ⟨x, ⟨e⟩⟩ := h ((homotopyFiniteCellToTria A D Set.univ).obj a)
  let q := (homotopyFiniteCellToTria A D Set.univ).preimageIso
    (e ≪≫ (dgHomotopyFiniteCellRepresentableTriaIso A D x).symm)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff A D M).2
    ⟨x, ⟨(homotopyFiniteCellOver A D Set.univ).ι.mapIso q⟩⟩

/-- 前三角 dg 圏の tria の全対象は代表対象と同型である。 -/
lemma dgTria_isRepresentable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (X : TriaCategory A D) :
    ∃ x : D, Nonempty (X ≅ triaRepresentable A D x) := by
  let E := homotopyFiniteCellTriaEquivalence A D Set.univ
  let a := E.inverse.obj X
  have ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D a.obj := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_eq_finiteCell A D]
    exact a.property
  obtain ⟨x, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff A D a.obj).1 ha
  refine ⟨x, ⟨(E.counitIso.app X).symm ≪≫ ?_⟩⟩
  exact (homotopyFiniteCellToTria A D Set.univ).mapIso
    ((homotopyFiniteCellOver A D Set.univ).isoMk e) ≪≫
      dgHomotopyFiniteCellRepresentableTriaIso A D x

/-- dg 前三角性は tria の全対象の代表可能性で判定できる。 -/
lemma isDGPretriangulated_iff_tria_representable :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D ↔
      ∀ X : TriaCategory A D, ∃ x : D, Nonempty (X ≅ triaRepresentable A D x) :=
  ⟨fun h => by let := h; exact dgTria_isRepresentable A D,
    isDGPretriangulated_of_tria_representable A D⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
