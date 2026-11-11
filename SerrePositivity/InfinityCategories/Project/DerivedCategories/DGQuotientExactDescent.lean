module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactFunctorDescent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientArrowLifts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientLocalization
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 商からの実関手は、商への制限が完全なら完全。 -/
lemma dgQuotient_isExactFunctor_of_precomp (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G)] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P hP
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.isExactFunctor_of_precomp_arrowLifts (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_arrow_lifts A D P hP) G
/-- 商からの実関手の完全性と、元の dg nerve への制限の完全性は同値。 -/
lemma dgQuotient_isExactFunctor_iff_precomp (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] (G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) := by
  constructor
  · intro hG
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P hP
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
  · intro hG
    exact dgQuotient_isExactFunctor_of_precomp A D P hP G
/-- 指定対象を零化する任意完全関手は、商上の完全関手と全関手圏の一つの同型を持つ。 -/
lemma dgVerdierExactFunctor_extension_exists (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {Y : SSet.{max u v}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (hF : ∀ b : P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val))) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor G ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) F) := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_inverts_iff_kills A D F P).mpr hF
  obtain ⟨G, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierInvertingFunctor_extension_iso_exists A D P hP F hi
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso e.symm
  exact ⟨G, dgQuotient_isExactFunctor_of_precomp A D P hP G, ⟨e⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
