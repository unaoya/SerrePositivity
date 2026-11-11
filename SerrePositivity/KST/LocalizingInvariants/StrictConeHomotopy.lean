module

public import SerrePositivity.KST.LocalizingInvariants.StrictConePrismComponent
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopySimplexFaces

/-!
概要：通常の錐の全比較から、元の二つの strict coherent 錐を結ぶ実ホモトピーを作る。
方針：始対象を加えた関手の prism を、同じ join の標準錐で制限する。
規約：頂点射も基底の比較も全 prism に保持。使われ方：BF fiber の実 cube の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

def shape (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      nerve (WithInitial (AsSmall.{v} I)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I))

lemma shape_inl (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v}) _ ≫ shape.{u, v} I =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (WithInitial.star : WithInitial (AsSmall.{v} I)) := by
  rw [shape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveInitialCone_left]

lemma shape_vertex (I : Type u) [SmallCategory I] :
    (shape.{u, v} I).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _)) =
      ComposableArrows.mk₀ (WithInitial.star : WithInitial (AsSmall.{v} I)) := by
  rw [← SSet.yonedaEquiv_comp, shape_inl]
  rfl

lemma precomp_component {A B X : SSet.{u}} (i : A ⟶ B) {F G : B ⟶ X}
    (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp i H) x).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) x)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_simplex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_simplex]
  change H.h.app (Opposite.op ⦋1⦌) (i.app _ (A.σ 0 x), _) =
    H.h.app (Opposite.op ⦋1⦌) (B.σ 0 (i.app _ x), _)
  exact congrArg (fun z ↦ H.h.app (Opposite.op ⦋1⦌)
    (z, SSet.yonedaEquiv (𝟙 Δ[1])))
      (ConcreteCategory.congr_hom (i.naturality (SimplexCategory.σ 0).op) x)

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C} (η : F ⟶ G) (c : Cone F) (d : Cone G)
  (m : c.pt ⟶ d.pt) (hm : ∀ i, c.π.app i ≫ η.app i = m ≫ d.π.app i)

def homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c).val (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone d).val :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (shape I) (largeHomotopy (transformation η c d m hm))

lemma homotopy_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopy η c d m hm)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge m).edge := by
  rw [homotopy, precomp_component, shape_vertex, largeHomotopy_component]
  rfl

end SerrePositivity.KST.LocalizingInvariants.StrictConeMap
