module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Complexes.UnitBoundary
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Quotient.Linear

/-! # dg 圏の H⁰

Z⁰ の単位からの射のホモトピーで商を取る。
単位は次数零に集中するので、この関係は Hom 複体の −1 境界による関係に一致する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉次数零射を結ぶ chain homotopy。境界を同一視する関係。 -/
def boundaryRelation : HomRel (ClosedCategory A D) :=
  fun _ _ f g => Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
    (ForgetEnrichment.homTo (Complex A) g))

/-- 境界関係は合成に安定な同値関係。
合成との両立は tensor によるホモトピーの写像から証明する。 -/
instance boundaryCongruence : Congruence (boundaryRelation A D) where
  equivalence :=
    { refl := fun f => ⟨Homotopy.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩ }
  comp_left := by
    intro x y z f g g' hh
    obtain ⟨h⟩ := hh
    refine ⟨?_⟩
    exact ((mapBifunctorMapHomotopy₂ (ForgetEnrichment.homTo (Complex A) f) h
      (curriedTensor (ModuleCat A)) (.up ℤ)).compLeft (λ_ _).inv).compRight
      (eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
  comp_right := by
    intro x y z f f' g hh
    obtain ⟨h⟩ := hh
    refine ⟨?_⟩
    exact ((mapBifunctorMapHomotopy₁ h (ForgetEnrichment.homTo (Complex A) g)
      (curriedTensor (ModuleCat A)) (.up ℤ)).compLeft (λ_ _).inv).compRight
      (eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))

/-- 境界関係は加法と両立する。 -/
lemma boundary_add {x y : ClosedCategory A D} (f f' g g' : x ⟶ y)
    (hf : boundaryRelation A D f f') (hg : boundaryRelation A D g g') :
    boundaryRelation A D (f + g) (f' + g') :=
  ⟨hf.some.add hg.some⟩

/-- 境界関係は任意の A スカラーと両立する。 -/
lemma boundary_smul (a : A) {x y : ClosedCategory A D} (f g : x ⟶ y)
    (h : boundaryRelation A D f g) : boundaryRelation A D (a • f) (a • g) :=
  ⟨h.some.smul a⟩

/-- H⁰ の対象は D の対象、射は Z⁰ の境界による商。 -/
abbrev HomotopyCategory := CategoryTheory.Quotient (boundaryRelation A D)

/-- H⁰ の合成は境界商上 well-defined で、加法的。 -/
instance homotopyPreadditive : Preadditive (HomotopyCategory A D) :=
  Quotient.preadditive _ (fun {x y} => boundary_add A D (x := x) (y := y))

/-- Z⁰ から H⁰ への商関手。 -/
abbrev toHomotopy : ClosedCategory A D ⥤ HomotopyCategory A D :=
  Quotient.functor (boundaryRelation A D)

/-- 商関手は加法を保存する。 -/
instance toHomotopyAdditive : (toHomotopy A D).Additive :=
  Quotient.functor_additive _ (fun {x y} => boundary_add A D (x := x) (y := y))

/-- H⁰ は A 線形。商のスカラー作用を Mathlib で構成する。 -/
instance homotopyLinear : Linear A (HomotopyCategory A D) :=
  Quotient.linear A _ (boundary_smul A D)

/-- 商関手は A 線形。 -/
instance toHomotopyLinear : (toHomotopy A D).Linear A :=
  Quotient.linear_functor A (boundaryRelation A D) (boundary_smul A D)

/-- H⁰ での等式は、ちょうど境界関係による等式である。 -/
lemma toHomotopy_map_eq_iff {x y : ClosedCategory A D} (f g : x ⟶ y) :
    (toHomotopy A D).map f = (toHomotopy A D).map g ↔ boundaryRelation A D f g :=
  Quotient.functor_map_eq_iff _ _ _
/-- H⁰ の等式は、元の Hom 複体の −1 境界による差に一致する。 -/
lemma toHomotopy_map_eq_iff_boundary {x y : ClosedCategory A D} (f g : x ⟶ y) :
    (toHomotopy A D).map f = (toHomotopy A D).map g ↔
      ∃ h : (homObject A D x y).X (-1),
        (homObject A D x y).d (-1) 0 h =
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val -
            (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val := by
  rw [toHomotopy_map_eq_iff]
  exact unit_homotopy_boundary _ _ _

/-- Z⁰ の射を閉次数零の元として読む同値。 -/
def closedHomEquiv (x y : ClosedCategory A D) :
    (x ⟶ y) ≃ zeroCycles (homObject A D x y) := unitCycleEquiv _

end SerrePositivity.DifferentialGraded
