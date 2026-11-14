module

public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientZeroObjects

/-!
概要：商合成を、始域の全対象を殺す実 dg 商を経由する厳密な四角形にする。
方針：像対象の指定 ε を用い、D 正本の指定収縮付き商普遍性を適用する。
規約：対象別 ε の自然性を仮定しない。零角は一対象の零 dg 圏へ置換しない。
使われ方：固定 dg 提示源内の相対 Verdier 四角形の零角候補。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable (R : Type u) [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor R D E)

/-- 元の始域の全対象を殺す、小ささを保持した零角候補。 -/
abbrev dgNullCorner := DGQuotient.QuotientObject D (Set.univ : Set D)

/-- 元の包含後の商合成に、像対象の同じ ε を指定する。 -/
def dgQuotientCompositeContracted :
    DGQuotient.ContractedFunctor R D Set.univ
      (DGQuotient.QuotientObject E (Set.range F.obj)) where
  toDGFunctor := F.comp (DGQuotient.inclusion R E (Set.range F.obj))
  homotopy x := DGQuotient.epsilonElement R E (Set.range F.obj)
    ⟨F.obj x.val, ⟨x.val, rfl⟩⟩
  d_homotopy x := DGQuotient.differential_epsilonElement R E (Set.range F.obj)
    ⟨F.obj x.val, ⟨x.val, rfl⟩⟩

/-- 始域の全対象商から、元の像対象商への実 dg 延長。 -/
def dgNullCornerComparison :
    DGFunctor R (dgNullCorner (D := D))
      (DGQuotient.QuotientObject E (Set.range F.obj)) :=
  DGQuotient.extension R (dgQuotientCompositeContracted R F)

/-- 元の二射と零角経由の二射は、全 Hom 上で厳密に一致する。 -/
lemma dgNullCorner_composite :
    (DGQuotient.inclusion R D Set.univ).comp (dgNullCornerComparison R F) =
      F.comp (DGQuotient.inclusion R E (Set.range F.obj)) :=
  DGQuotient.inclusion_comp_extension R (dgQuotientCompositeContracted R F)

/-- 零角の指定 ε の像は、元の像対象の ε そのもの。 -/
lemma dgNullCornerComparison_epsilon (x : D) :
    ((dgNullCornerComparison R F).map ⟨x⟩ ⟨x⟩).f (-1)
      (DGQuotient.epsilonElement R D Set.univ ⟨x, Set.mem_univ x⟩) =
      DGQuotient.epsilonElement R E (Set.range F.obj) ⟨F.obj x, ⟨x, rfl⟩⟩ :=
  DGQuotient.restrict_extension_homotopy R (dgQuotientCompositeContracted R F)
    ⟨x, Set.mem_univ x⟩

/-- 全対象商の元の対象は、同じ dg nerve の実零頂点。Perf 値の零性は別の接続。 -/
lemma dgNullCorner_vertex_isZero (x : dgNullCorner (D := D)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve R D Set.univ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledVertex_isZero R D Set.univ ⟨x.val, Set.mem_univ x.val⟩

end SerrePositivity.KST.LocalizingInvariants
