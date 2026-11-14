module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.ResolutionComparisons.DeformationHomNaturality
/-!
概要：同じ指定変形降下比較と制限比較の自然性を、全関手同型として証明する。
方針：元の指定値と同じ実変形円柱を保って照合する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 比較 ξ の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- 同じ実変形降下比較は、任意の指定全関手同型に自然。 -/
lemma deformationFunctorDescentIso_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T U : X ⟶ Y) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges T W) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U W)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T U) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT ≪≫ a =
      (a.precomp I).precomp L ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH U hU := by
  apply Iso.ext
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy_naturality L I H a

/-- 同じ制限比較の自然性正方形は、実変形降下との合成へ移る。 -/
lemma deformationComparisonIso_naturality {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T U : X ⟶ Y) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges T W) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U W)
    {K K' : D ⟶ Y} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ T)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K' (I ≫ U))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K K') (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T U)
    (hs : b ≪≫ s = r ≪≫ a.precomp I) :
    (r.precomp L ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT) ≪≫ a =
      b.precomp L ≪≫ (s.precomp L ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH U hU) := by
  calc
    _ = r.precomp L ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT ≪≫ a) :=
      Iso.trans_assoc _ _ _
    _ = r.precomp L ≪≫ ((a.precomp I).precomp L ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH U hU) := by
      rw [deformationFunctorDescentIso_naturality]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (r ≪≫ a.precomp I) L ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH U hU := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (b ≪≫ s) L ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH U hU := by
      rw [← hs]
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
