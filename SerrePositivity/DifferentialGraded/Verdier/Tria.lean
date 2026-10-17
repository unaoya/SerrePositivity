module
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty
public import SerrePositivity.CategoryTheory.VerdierKaroubiLinear

/-! # 既存の有限 cell 本質像としての tria(D)

tria は retract を加える前の三角部分圏であり、Perf とは区別する。
部分集合 S は、後続の明示的 dg 商で殺す full 部分圏と同じ対象添字である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存の有限 cell 本質像の充満三角部分圏 tria(D)。 -/
abbrev TriaCategory := DerivedFiniteCellCategoryOver A D Set.univ

abbrev triaInclusion : TriaCategory A D ⥤ DerivedModuleCategory A D :=
  derivedFiniteCellInclusion A D Set.univ

/-- tria(D) 内で考える、S の代表加群からの三角閉包。 -/
def triaImage (S : Set D) : ObjectProperty (TriaCategory A D) :=
  (derivedFiniteCellOver A D S).inverseImage (triaInclusion A D)

instance triaImageClosedUnderIso (S : Set D) :
    (triaImage A D S).IsClosedUnderIsomorphisms := by
  dsimp [triaImage]
  infer_instance

instance triaImageIsTriangulated (S : Set D) : (triaImage A D S).IsTriangulated := by
  dsimp [triaImage]
  infer_instance

/-- tria(D) の指定代表対象。 -/
def triaRepresentable (x : D) : TriaCategory A D :=
  ⟨(moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)),
    (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCell_representable A D x)⟩

lemma triaImage_representable (S : Set D) (x : D) (hx : x ∈ S) :
    triaImage A D S (triaRepresentable A D x) :=
  (moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCellOver_representable A D x hx)

/-- tria(D) 内の三角部分圏に対する生成性。 -/
lemma triaImage_le_iff_generators (S : Set D)
    (P : ObjectProperty (TriaCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] :
    triaImage A D S ≤ P ↔ ∀ x ∈ S, P (triaRepresentable A D x) := by
  constructor
  · intro h x hx
    exact h _ (triaImage_representable A D S x hx)
  · intro h X hX
    have hle : derivedFiniteCellOver A D S ≤ P.map (triaInclusion A D) :=
      (derivedFiniteCellOver_le_iff_generators A D
        (P.map (triaInclusion A D)) S).2
        (fun x hx => P.prop_map_obj (triaInclusion A D) (h x hx))
    obtain ⟨Y, hY, ⟨e⟩⟩ := hle _ hX
    exact P.prop_of_iso ((triaInclusion A D).preimageIso e) hY

/-- 後続の Karoubi/Verdier 比較で使う厚い零対象クラス。 -/
abbrev triaNull (S : Set D) : ObjectProperty (TriaCategory A D) :=
  (triaImage A D S).triangEnvelope

/-- tria(D)/tria(S) の既存の指定 Verdier 局所化。 -/
abbrev TriaQuotient (S : Set D) := (triaImage A D S).trW.Localization

abbrev triaQuotient (S : Set D) : TriaCategory A D ⥤ TriaQuotient A D S :=
  (triaImage A D S).trW.Q

/-- U17b の比較先。局所化・Karoubi の新しい一般構成を導入しない。 -/
abbrev CompletedTriaQuotient (S : Set D) :=
  CategoryTheory.Idempotents.Karoubi (TriaQuotient A D S)

/-- U17c の既存の順序交換同値に渡す、同じ三角部分圏。 -/
abbrev triaKaroubiOrderEquivalence (S : Set D) :
    CategoryTheory.Idempotents.Karoubi (KaroubiFirstQuotient (triaImage A D S)) ≌
      CompletedTriaQuotient A D S :=
  karoubiVerdierOrderEquivalence (triaImage A D S)

/-- 完備化を先に行う側の標準関手。 -/
abbrev triaKaroubiFirst (S : Set D) := karoubiFirstFromOriginal (triaImage A D S)

/-- `paperSequenceComparison` と同じ向きの標準関手の比較。 -/
def triaKaroubiComparison (S : Set D) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ≅
      triaQuotient A D S ⋙ CategoryTheory.Idempotents.toKaroubi _ :=
  isoWhiskerLeft (CategoryTheory.Idempotents.toKaroubi _ ⋙
      (karoubiNullEnvelope (triaImage A D S)).trW.Q)
    (completedKaroubiFirstToLastFactors _) ≪≫
  isoWhiskerLeft (CategoryTheory.Idempotents.toKaroubi _) (karoubiFirstToLastFactors _) ≪≫
  (CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
    (triaQuotient A D S)

end SerrePositivity.DifferentialGraded
