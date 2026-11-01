module
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactFunctorDescent
public import SerrePositivity.InfinityCategories.Derived.DGQuotientArrowLifts
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalization
/-!
概要：平坦 dg 商からの実関手の完全性は、元の dg nerve への制限で判定できる。
方針：商の実分数三角形から全実辺の同型表示を得て、元の cofiber の像で反映する。
規約：延長関手の完全性を追加仮定にしない。使われ方：零化完全関手圏の Verdier 普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 商からの実関手は、商への制限が完全なら完全。 -/
lemma dgQuotient_isExactFunctor_of_precomp (P : Set D) (hP : DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : dgQuotientNerve A D P ⟶ Y)
    [IsExactFunctor (dgQuotientNerveProjection A D P ≫ G)] : IsExactFunctor G := by
  let := dgNerve_isStable_of_pretriangulated A D
  let := dgQuotientNerveProjection_isExactFunctor A D P hP
  exact isExactFunctor_of_precomp_arrowLifts (dgQuotientNerveProjection A D P)
    (dgQuotientNerveProjection_arrow_lifts A D P hP) G
/-- 商からの実関手の完全性と、元の dg nerve への制限の完全性は同値。 -/
lemma dgQuotient_isExactFunctor_iff_precomp (P : Set D) (hP : DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : dgQuotientNerve A D P ⟶ Y) :
    IsExactFunctor G ↔ IsExactFunctor (dgQuotientNerveProjection A D P ≫ G) := by
  constructor
  · intro hG
    let := dgQuotientNerveProjection_isExactFunctor A D P hP
    exact isExactFunctor_comp _ _
  · intro hG
    exact dgQuotient_isExactFunctor_of_precomp A D P hP G
/-- 指定対象を零化する任意完全関手は、商上の完全関手と全関手圏の一つの同型を持つ。 -/
lemma dgVerdierExactFunctor_extension_exists (P : Set D) (hP : DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] [IsStable Y]
    (F : dgNerve A D ⟶ Y) [IsExactFunctor F]
    (hF : ∀ b : P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex b.val))) :
    ∃ G : dgQuotientNerve A D P ⟶ Y,
      IsExactFunctor G ∧ Nonempty (FunctorIso (dgQuotientNerveProjection A D P ≫ G) F) := by
  have hi := (dgVerdierEdges_inverts_iff_kills A D F P).mpr hF
  obtain ⟨G, ⟨e⟩⟩ := dgVerdierInvertingFunctor_extension_iso_exists A D P hP F hi
  have : IsExactFunctor (dgQuotientNerveProjection A D P ≫ G) :=
    isExactFunctor_of_functorIso e.symm
  exact ⟨G, dgQuotient_isExactFunctor_of_precomp A D P hP G, ⟨e⟩⟩
end SerrePositivity.InfinityCategories
