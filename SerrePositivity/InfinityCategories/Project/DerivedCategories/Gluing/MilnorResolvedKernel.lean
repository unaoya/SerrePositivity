module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFlatThickTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientThickLocalization
/-!
概要：Milnor 対角の本質像を同じ cell 平坦商の零対象核として同定する。
方針：実平坦 thick 核を元 gluing へ運び、元対角の thick 本質像判定を適用する。
規約：D-17 の生成判定と D-18 の前三角性・完全性を明示し、元対角を保持する。
使われ方：cell 平坦商の Verdier 列の kernel・localization 欄。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)]
lemma dgGluingMilnorResolvedQuotient_zero_iff
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotientFunctor R d).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal).app
          (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro hb
    obtain ⟨a, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R
      (DGOdotGluing R d) (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) b).mp hb
    obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective a
    have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonal_flatThick_image R d x.val x.property
    obtain ⟨a, ⟨ea⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonal_thickClosure_iff_image R d h hgen _).mp hx
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) a, ?_⟩
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e ⊢
    exact ⟨ea.trans e⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective a
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotient_kills_diagonal R d a).of_vertexIso
      (e.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotientFunctor R d))
lemma dgGluingMilnorResolvedQuotient_isLocalization
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotientFunctor R d)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal).app
            (Opposite.op ⦋0⦌) a) b)}) := by
  have he := Set.ext (fun b =>
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) b).symm.trans
        (dgGluingMilnorResolvedQuotient_zero_iff R d h hgen b))
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isThickLocalization R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
  rw [he] at hl
  exact hl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
