module

public import SerrePositivity.HomologicalAlgebra.StupidTruncation
public import SerrePositivity.CategoryTheory.BoundedHomotopyGeneration

/-! # 項ごとの切り詰めの有界ホモトピー圏での完全三角形 -/

@[expose] public section

universe v u v' u'

namespace SerrePositivity.StupidTruncation

open CategoryTheory Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

omit [HasBinaryBiproducts C] in
lemma above_bounded (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (a : ℤ) :
    strictlyBoundedComplex C (above K a) := by
  obtain ⟨b, c, hb, hc⟩ := hK
  exact ⟨b, c, inferInstance, inferInstance⟩

omit [HasBinaryBiproducts C] in
lemma below_bounded (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (b : ℤ) :
    strictlyBoundedComplex C (below K b) := by
  obtain ⟨a, c, ha, hc⟩ := hK
  exact ⟨a, c, inferInstance, inferInstance⟩

/-- 切り詰めの包含を有界ホモトピー圏で見る。 -/
noncomputable def boundedInclusion (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) :
    boundedComplexObj (above K a) (above_bounded K hK a) ⟶ boundedComplexObj K hK :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (inclusion K a))

/-- 切り詰めとその尾部を結ぶ、有界ホモトピー圏の完全三角形。 -/
noncomputable def boundedTriangle (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) : Triangle (BoundedHomotopy C) :=
  fullSubcategoryTriangle (boundedHomotopyProperty C)
    (CochainComplex.trianglehOfDegreewiseSplit (shortComplex K a) (splitting K a))
    ((boundedHomotopyProperty_quotient _ _).mpr (above_bounded K hK a))
    ((boundedHomotopyProperty_quotient _ _).mpr hK)
    ((boundedHomotopyProperty_quotient _ _).mpr (below_bounded K hK (a - 1)))

lemma boundedTriangle_distinguished (K : CochainComplex C ℤ)
    (hK : strictlyBoundedComplex C K) (a : ℤ) :
    boundedTriangle K hK a ∈ distTriang (BoundedHomotopy C) :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished (shortComplex K a) (splitting K a))

/-- 尾部を零に送る三角関手は、切り詰めの包含を同型に送る。 -/
lemma isIso_map_boundedInclusion
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : BoundedHomotopy C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (K : CochainComplex C ℤ) (hK : strictlyBoundedComplex C K) (a : ℤ)
    (hz : IsZero (T.obj (boundedComplexObj (below K (a - 1))
      (below_bounded K hK (a - 1))))) : IsIso (T.map (boundedInclusion K hK a)) :=
  (Triangle.isZero₃_iff_isIso₁ _ (T.map_distinguished _
    (boundedTriangle_distinguished K hK a))).mp hz

end SerrePositivity.StupidTruncation
