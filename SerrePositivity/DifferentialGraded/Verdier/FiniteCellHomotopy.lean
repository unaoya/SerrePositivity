module
public import SerrePositivity.DifferentialGraded.Verdier.Tria
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles

/-! # 有限 cell の K(D) 内の像と tria(D) の三角同値

有限 cell の射影性により、主導来局所化はこの部分圏上で完全忠実となる。
dg 圏の解像度は用いない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- retract を加えない有限 cell の K(D) 内の本質像。 -/
def homotopyFiniteCellOver (S : Set D) : ObjectProperty (ModuleHomotopyCategory A D) :=
  (moduleFiniteCellOver A D S).map (moduleToHomotopy A D)

instance homotopyFiniteCellOverClosedUnderIso (S : Set D) :
    (homotopyFiniteCellOver A D S).IsClosedUnderIsomorphisms := by
  dsimp [homotopyFiniteCellOver]
  infer_instance

instance homotopyFiniteCellOverShift (S : Set D) :
    (homotopyFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro X ⟨M, hM, ⟨e⟩⟩
    exact ⟨M⟦n⟧, moduleFiniteCellOver_shift A D hM n,
      ⟨((moduleToHomotopy A D).commShiftIso n).app M ≪≫
        (shiftFunctor _ n).mapIso e⟩⟩⟩

lemma homotopyFiniteCellOver_triangle_obj₃ (S : Set D)
    (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (ModuleHomotopyCategory A D))
    (h₁ : homotopyFiniteCellOver A D S T.obj₁)
    (h₂ : homotopyFiniteCellOver A D S T.obj₂) : homotopyFiniteCellOver A D S T.obj₃ := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := h₁
  obtain ⟨N, hN, ⟨eN⟩⟩ := h₂
  obtain ⟨f, hf⟩ := (moduleToHomotopy A D).map_surjective (eM.hom ≫ T.mor₁ ≫ eN.inv)
  have he : Arrow.mk (moduleHomotopyConeTriangle A D f).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk eM eN (by
      change eM.hom ≫ T.mor₁ = (moduleToHomotopy A D).map f ≫ eN.hom
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (moduleHomotopyConeTriangle A D f) T
    (moduleHomotopyConeTriangle_distinguished A D f) hT he
  exact ⟨moduleCone A D f, moduleFiniteCellOver_cone A D hM hN f, ⟨Triangle.π₃.mapIso e⟩⟩

instance homotopyFiniteCellOverClosed₃ (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (homotopyFiniteCellOver_triangle_obj₃ A D S)

instance homotopyFiniteCellOverClosed₂ (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance homotopyFiniteCellOverContainsZero (S : Set D) :
    (homotopyFiniteCellOver A D S).ContainsZero :=
  ⟨⟨(moduleToHomotopy A D).obj (moduleZero A D),
    (moduleToHomotopy A D).map_isZero (moduleZero_isZero A D),
    (moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCellOver_zero A D S)⟩⟩

instance homotopyFiniteCellOverIsTriangulated (S : Set D) :
    (homotopyFiniteCellOver A D S).IsTriangulated where

abbrev HomotopyFiniteCellCategoryOver (S : Set D) := (homotopyFiniteCellOver A D S).FullSubcategory

/-- 有限 cell の像を始域とする局所化 Hom 写像は全単射。 -/
lemma homotopyFiniteCell_localization_map_bijective {S : Set D}
    {X : ModuleHomotopyCategory A D} (hX : homotopyFiniteCellOver A D S X)
    (Y : ModuleHomotopyCategory A D) :
    Function.Bijective ((moduleHomotopyToDerivedClosed A D).map (X := X) (Y := Y)) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hX
  let L := moduleHomotopyToDerivedClosed A D
  have hb := moduleProjectiveLocalization_map_bijective A D
    (moduleFiniteCellOver_homotopicallyProjective A D hM) Y
  constructor
  · intro f g h
    have hh : e.hom ≫ f = e.hom ≫ g := hb.1 (by
      simp only [CategoryTheory.Functor.map_comp, h])
    exact (cancel_epi e.hom).mp hh
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (L.map e.hom ≫ f)
    refine ⟨e.inv ≫ g, ?_⟩
    rw [CategoryTheory.Functor.map_comp, hg]
    change L.map e.inv ≫ L.map e.hom ≫ f = f
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- K(D) から主導来圏への既存関手の有限 cell 部分圏上の制限。 -/
def homotopyFiniteCellToDerived (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (homotopyFiniteCellOver A D S).ι ⋙ moduleHomotopyToDerivedClosed A D

instance homotopyFiniteCellToDerivedFull (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (homotopyFiniteCell_localization_map_bijective A D X.property Y.obj).2 f
    refine ⟨(homotopyFiniteCellOver A D S).ι.preimage g, ?_⟩
    change (moduleHomotopyToDerivedClosed A D).map
      ((homotopyFiniteCellOver A D S).ι.map ((homotopyFiniteCellOver A D S).ι.preimage g)) = f
    rw [Functor.map_preimage]
    exact hg

instance homotopyFiniteCellToDerivedFaithful (S : Set D) :
    (homotopyFiniteCellToDerived A D S).Faithful where
  map_injective {X Y} f g h := by
    apply (homotopyFiniteCellOver A D S).ι.map_injective
    exact (homotopyFiniteCell_localization_map_bijective A D X.property Y.obj).1 h

lemma homotopyFiniteCellToDerived_mem (S : Set D) (X : HomotopyFiniteCellCategoryOver A D S) :
    derivedFiniteCellOver A D S ((homotopyFiniteCellToDerived A D S).obj X) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := X.property
  exact ⟨M, hM, ⟨((moduleToHomotopyDerivedIso A D).app M).symm ≪≫
    (moduleHomotopyToDerivedClosed A D).mapIso e⟩⟩

/-- 有限 cell 同士では主導来局所化は三角同値。 -/
def homotopyFiniteCellToTria (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ⥤ DerivedFiniteCellCategoryOver A D S :=
  (derivedFiniteCellOver A D S).lift (homotopyFiniteCellToDerived A D S)
    (homotopyFiniteCellToDerived_mem A D S)

instance homotopyFiniteCellToTriaFull (S : Set D) :
    (homotopyFiniteCellToTria A D S).Full := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaFaithful (S : Set D) :
    (homotopyFiniteCellToTria A D S).Faithful := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaEssSurj (S : Set D) :
    (homotopyFiniteCellToTria A D S).EssSurj where
  mem_essImage X := by
    obtain ⟨M, hM, ⟨e⟩⟩ := X.property
    exact ⟨⟨(moduleToHomotopy A D).obj M,
      (moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D) hM⟩,
      ⟨(derivedFiniteCellOver A D S).isoMk ((moduleToHomotopyDerivedIso A D).app M ≪≫ e)⟩⟩

instance homotopyFiniteCellToTriaIsEquivalence (S : Set D) :
    (homotopyFiniteCellToTria A D S).IsEquivalence where

instance homotopyFiniteCellToDerivedCommShift (S : Set D) :
    (homotopyFiniteCellToDerived A D S).CommShift ℤ := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance

instance homotopyFiniteCellToDerivedIsTriangulated (S : Set D) :
    (homotopyFiniteCellToDerived A D S).IsTriangulated := by
  dsimp [homotopyFiniteCellToDerived]
  infer_instance

instance homotopyFiniteCellToTriaCommShift (S : Set D) :
    (homotopyFiniteCellToTria A D S).CommShift ℤ := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

instance homotopyFiniteCellToTriaIsTriangulated (S : Set D) :
    (homotopyFiniteCellToTria A D S).IsTriangulated := by
  dsimp [homotopyFiniteCellToTria]
  infer_instance

def homotopyFiniteCellTriaEquivalence (S : Set D) :
    HomotopyFiniteCellCategoryOver A D S ≌ DerivedFiniteCellCategoryOver A D S :=
  (homotopyFiniteCellToTria A D S).asEquivalence

instance homotopyFiniteCellTriaEquivalenceFunctorCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).functor.CommShift ℤ :=
  homotopyFiniteCellToTriaCommShift A D S

instance homotopyFiniteCellTriaEquivalenceInverseCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).inverse.CommShift ℤ :=
  (homotopyFiniteCellTriaEquivalence A D S).commShiftInverse ℤ

instance homotopyFiniteCellTriaEquivalenceCommShift (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).CommShift ℤ :=
  (homotopyFiniteCellTriaEquivalence A D S).commShift_of_functor ℤ

instance homotopyFiniteCellTriaEquivalenceIsTriangulated (S : Set D) :
    (homotopyFiniteCellTriaEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (homotopyFiniteCellToTriaIsTriangulated A D S)

end SerrePositivity.DifferentialGraded
