module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCells
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGenerators

/-! # tria(D) 全体から明示的 dg 商の tria への比較

対象は加群の射影置換で扱う。局所 K-flat 下の Verdier 比較の完全忠実性は別段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits ZeroObject Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空 path の包含に沿う導来拡張を tria(D) 上で考える。 -/
def derivedComparisonFromTria (S : Set D) :
    TriaCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  triaInclusion A D ⋙ dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)

lemma derivedComparisonFromTria_finiteCell (S : Set D) (X : TriaCategory A D) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedComparisonFromTria A D S).obj X) :=
  graphDerivedExtension_derivedFiniteCell_mem A D (QuotientObject D S) (inclusion A D S)
    (derivedFiniteCellOver A (QuotientObject D S) Set.univ) Set.univ
    (fun x _ => (moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
      (moduleToDerived A (QuotientObject D S))
      (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩)) X.property

/-- tria の対象と射の全体に定義された比較関手。 -/
def derivedComparisonTria (S : Set D) : TriaCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedComparisonFromTria A D S) (derivedComparisonFromTria_finiteCell A D S)

/-- 比較関手の代表対象上での計算。 -/
def derivedComparisonTria_representableIso (S : Set D) (x : D) :
    (derivedComparisonTria A D S).obj (triaRepresentable A D x) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    (dgDerivedExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x)

/-- B の代表対象からの有限三角操作も、商側では全て零となる。 -/
lemma derivedComparisonFromTria_kills (S : Set D) (X : TriaCategory A D)
    (hX : triaImage A D S X) : IsZero ((derivedComparisonFromTria A D S).obj X) := by
  let P : ObjectProperty (DerivedModuleCategory A (QuotientObject D S)) := IsZero
  let : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h => h.of_iso e.symm⟩
  let : P.IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun _ h => (shiftFunctor _ n).map_isZero h⟩⟩
  let : P.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, isZero_zero _⟩
      ext₂' := fun T hT h₁ h₃ =>
        ⟨T.obj₂, T.isZero₂_of_isZero₁₃ hT h₁ h₃, ⟨Iso.refl _⟩⟩ }
  exact graphDerivedExtension_derivedFiniteCell_mem A D (QuotientObject D S) (inclusion A D S)
    P S (fun x hx => quotientRepresentable_derived_isZero A D S ⟨x, hx⟩) hX

/-- 値域を tria に制限しても、同じ零性を保つ。 -/
lemma derivedComparisonTria_kills (S : Set D) (X : TriaCategory A D)
    (hX : triaImage A D S X) : IsZero ((derivedComparisonTria A D S).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply (triaInclusion A (QuotientObject D S)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (derivedComparisonFromTria_kills A D S X hX).eq_of_src _ _

/-- この比較の代表対象の像は商側の tria を三角生成する。 -/
lemma derivedComparisonTria_generates (S : Set D)
    (P : ObjectProperty (TriaCategory A (QuotientObject D S)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ x : D, P ((derivedComparisonTria A D S).obj (triaRepresentable A D x)))
    (X : TriaCategory A (QuotientObject D S)) : P X := by
  have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ P).2
    (fun x _ => P.prop_of_iso (derivedComparisonTria_representableIso A D S x.val) (hP x.val))
  exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
