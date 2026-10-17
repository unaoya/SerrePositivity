module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction
public import SerrePositivity.DifferentialGraded.Verdier.Tria

/-! # 空 path 包含による代表対象上の実際の導来比較

商への dg 関手、dg Yoneda、既存の主局所化の合成を使う。
tria(D) 全体への延長と Verdier 商上の完全忠実性は後続で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の H⁰ から商の導来圏へ、明示的包含と Yoneda で定まる比較。 -/
def derivedComparisonOnGenerators (S : Set D) :
    HomotopyCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (inclusion A D S).onHomotopy ⋙ (dgYoneda A (QuotientObject D S)).onHomotopy ⋙
    moduleHomotopyToDerivedClosed A (QuotientObject D S)

def derivedComparisonOnGenerators_objIso (S : Set D) (x : D) :
    (derivedComparisonOnGenerators A D S).obj
        ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) ≅
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨x⟩ : QuotientObject D S))) :=
  (moduleToHomotopyDerivedIso A (QuotientObject D S)).app _

lemma derivedComparisonOnGenerators_finiteCell (S : Set D) (X : HomotopyCategory A D) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedComparisonOnGenerators A D S).obj X) := by
  obtain ⟨x⟩ := X
  exact (derivedFiniteCellOver A (QuotientObject D S) Set.univ).prop_of_iso
    (derivedComparisonOnGenerators_objIso A D S x).symm
    ((moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
      (moduleToDerived A (QuotientObject D S))
      (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩))

/-- 比較の値域を U17a と同じ tria の対象型に制限する。 -/
def derivedComparisonGeneratorsToTria (S : Set D) :
    HomotopyCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedComparisonOnGenerators A D S) (derivedComparisonOnGenerators_finiteCell A D S)

def derivedComparisonGeneratorsToTria_objIso (S : Set D) (x : D) :
    (derivedComparisonGeneratorsToTria A D S).obj
        ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x)) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    (derivedComparisonOnGenerators_objIso A D S x)

lemma derivedComparisonOnGenerators_kills (S : Set D) (b : S) :
    IsZero ((derivedComparisonOnGenerators A D S).obj
      ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) b.val))) :=
  (quotientRepresentable_derived_isZero A D S b).of_iso
    (derivedComparisonOnGenerators_objIso A D S b.val)

/-- 比較の代表像は、商側の tria 全体を三角生成する。retract を追加しない。 -/
lemma derivedComparisonGenerators_generate (S : Set D)
    (P : ObjectProperty (TriaCategory A (QuotientObject D S)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ x : D, P ((derivedComparisonGeneratorsToTria A D S).obj
      ((toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x))))
    (X : TriaCategory A (QuotientObject D S)) : P X := by
  have hle : triaImage A (QuotientObject D S) Set.univ ≤ P :=
    (triaImage_le_iff_generators A (QuotientObject D S) Set.univ P).2
      (fun x _ => P.prop_of_iso (derivedComparisonGeneratorsToTria_objIso A D S x.val)
        (hP x.val))
  exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
