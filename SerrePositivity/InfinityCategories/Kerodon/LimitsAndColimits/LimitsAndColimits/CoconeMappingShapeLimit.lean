module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingShapePushout
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks

/-!
概要：形状の押し出しで得る固定頂点の余錐空間は、空間の ∞ 圏でも部分余錐空間の極限。
方針：厳密な引き戻し錐を Kan 対象へ束ね、単射な境界の制限の fibration 性を適用する。
規約：右部分形状への共通境界の射の単射性を要求する。値域は任意の quasicategory。
使われ方：部分余極限を表現する Hom と、元の余錐空間の普遍性を比較する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section

/-- 任意の quasicategory 内の固定頂点の余錐空間を、束縛された Kan 対象とする。 -/
def coconeMappingKanObject {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X)
    (y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y⟩

variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (y : X _⦋0⦌)

/-- 右部分・左部分から共通境界への、固定頂点の余錐空間の Kan 値 cospan。 -/
def coconeMappingShapeDiagram : AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  AsSmall.down ⋙ cospan
    (show coconeMappingKanObject (j ≫ p) y ⟶ coconeMappingKanObject (f ≫ (i ≫ p)) y from
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y)
    (show coconeMappingKanObject (i ≫ p) y ⟶ coconeMappingKanObject (f ≫ (i ≫ p)) y from
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y)

/-- 元の固定頂点の余錐空間を頂点とする、台の単体集合での実際の引き戻し錐。 -/
def coconeMappingShapeUnderlyingCone :
    Cone (coconeMappingShapeDiagram hp p y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (Cone.postcompose (Functor.isoWhiskerLeft
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)
    (cospanCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget
      (show coconeMappingKanObject (j ≫ p) y ⟶ coconeMappingKanObject (f ≫ (i ≫ p)) y from
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y)
      (show coconeMappingKanObject (i ≫ p) y ⟶ coconeMappingKanObject (f ≫ (i ≫ p)) y from
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y))).inv).obj
    ((PullbackCone.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).w.symm).whisker
        (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan))

/-- 台の余錐空間の錐は、厳密な引き戻しの極限錐。 -/
def coconeMappingShapeUnderlyingCone_isLimit :
    IsLimit (coconeMappingShapeUnderlyingCone hp p y) := by
  apply (IsLimit.postcomposeInvEquiv _ _).symm.toFun
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).flip.isLimit.whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

/-- Kan 対象の圏で、元の余錐空間を頂点に持つ実際の錐。 -/
def coconeMappingShapeKanCone : Cone (coconeMappingShapeDiagram hp p y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying _ (coconeMappingShapeUnderlyingCone hp p y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y)

/-- 部分余錐空間の図式上に、元の余錐空間を頂点とする native な錐を作る。 -/
def coconeMappingShapeCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (coconeMappingShapeDiagram hp p y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (coconeMappingShapeKanCone hp p y)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _)

/-- native な錐の頂点は、元の図式の固定頂点余錐空間そのもの。 -/
lemma coconeMappingShapeCone_vertex :
    (coconeMappingShapeCone hp p y).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (coconeMappingKanObject p y) := by
  rw [coconeMappingShapeCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 単射な境界の押し出しに対し、元の余錐空間は空間の ∞ 圏での実際の極限。 -/
lemma coconeMappingShapeCone_isLimit [Mono g] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (coconeMappingShapeCone hp p y) := by
  have : ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (coconeMappingShapeDiagram hp p y) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z ↦ by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op Z)).map
      (show coconeMappingKanObject (j ≫ p) y ⟶ coconeMappingKanObject (f ≫ (i ≫ p)) y from
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y))
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration Z _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying_forget_isLimit _ _ _
    (coconeMappingShapeUnderlyingCone_isLimit hp p y)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
