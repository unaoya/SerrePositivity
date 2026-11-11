module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentShapeCoconeGluing
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FibrationComponentTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingRestriction

/-!
概要：形状の押し出しの二つの部分余錐が境界で同じ連結成分なら、単射側を直して厳密に貼る。
方針：終点固定の制限の Kan fibration 性で連結成分の一致を厳密な境界一致へ持ち上げる。
規約：左余錐と頂点を厳密に保ち、右余錐は同じ固定終点空間の連結成分に保つ。
使われ方：部分余極限対象の span の余錐から元の coherent 図式の余錐を組み立てる。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A B C D X : SSet.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}

/-- 右側の境界の図式を、押し出しの可換性で左側の同じ図式に正規化する。 -/
lemma coconePushoutBoundary_eq (hp : IsPushout f g i j) (p : D ⟶ X) :
    g ≫ (j ≫ p) = f ≫ (i ≫ p) := by
  rw [← Category.assoc, ← Category.assoc, hp.w]

/-- 右側の部分余錐の境界制限を、左側と同じ図式の固定終点空間に表示する。 -/
def coconePushoutRightBoundary (hp : IsPushout f g i j) (p : D ⟶ X) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (j ≫ p) g y ≫
    eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (coconePushoutBoundary_eq hp p))

/-- 境界での連結成分の一致から、左余錐を保つ実際の全体の余錐を構成できる。 -/
lemma exists_cocone_glue_of_boundary_component [Quasicategory X] (hp : IsPushout f g i j) [Mono g]
    (p : D ⟶ X) (y : X _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (i ≫ p) y) _⦋0⦌)
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y) _⦋0⦌)
    (h : SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y).app (Opposite.op ⦋0⦌) b) =
      SSet.π₀.mk ((coconePushoutRightBoundary hp p y).app (Opposite.op ⦋0⦌) c)) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, ∃ c' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y) _⦋0⦌,
      e.restrict i = b.val ∧ e.restrict j = c'.val ∧ e.vertex = y ∧
        SSet.π₀.mk c' = SSet.π₀.mk c := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (j ≫ p) g y) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_fibration (j ≫ p) g y
  have : Fibration (coconePushoutRightBoundary hp p y) := by
    dsimp only [coconePushoutRightBoundary]
    infer_instance
  obtain ⟨c', hc', hcc⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibration_vertex_in_component (coconePushoutRightBoundary hp p y)
    c ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y).app (Opposite.op ⦋0⦌) b) h.symm
  have ht {a a' : A ⟶ X} (ha : a = a')
      (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) _⦋0⦌) :
      (((eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) ha)).app
        (Opposite.op ⦋0⦌) s).val.val) = s.val.val := by
    cases ha
    rfl
  have hh := congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) y) _⦋0⦌ ↦ s.val.val) hc'
  change (((eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y)
    (coconePushoutBoundary_eq hp p))).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (j ≫ p) g y).app (Opposite.op ⦋0⦌) c')).val.val) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y).app (Opposite.op ⦋0⦌) b).val.val at hh
  rw [ht (coconePushoutBoundary_eq hp p)] at hh
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ≫ b.val.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 Δ[0]) ≫ c'.val.val := hh.symm
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentShapePushoutCocone hp p b.val c'.val hg
  refine ⟨e, c', _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentShapePushoutCocone_left _ _ _ _ _,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentShapePushoutCocone_right _ _ _ _ _, ?_, hcc⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentShapePushoutCocone_vertex]
  exact b.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
