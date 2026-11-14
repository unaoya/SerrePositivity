module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramMappingSpace
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.OppositeInternalHom

/-!
概要：strict な図式の全変換空間の反転を、反転した二図式間の全変換空間へ写す。
方針：各成分で元の内部 Hom の反転同型を使い、前後合成の自然性で条件を保つ。
規約：入力図式・変換空間の Kan 性を要求しない。
使われ方：元の反転豊穣 Hom 作用を、完成した左右区間比較のパラメーターへ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- strict な自然性は、内部 Hom の前後合成の単体そのものの等式。 -/
lemma strictDiagramMappingSimplex_post_pre {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} {n : SimplexCategoryᵒᵖ} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex F G n)
    {c d : C} (f : c ⟶ d) :
    ((ihom (F.obj c)).map (G.map f)).app n (η.val c) =
      ((pre (F.map f)).app (G.obj d)).app n (η.val d) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  change (G.map f).app k ((η.val c).app k α x) =
    (η.val d).app k (α ≫ 𝟙 k) ((F.map f).app k x)
  rw [Category.comp_id]
  exact η.property f k α x

/-- 内部 Hom の反転を全成分に適用した、反転した図式間の同じ次数の変換。 -/
def strictDiagramOppositeHomSimplex {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) {n : SimplexCategoryᵒᵖ}
    (η : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G).op.obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (F ⋙ SSet.opFunctor) (G ⋙ SSet.opFunctor) n := by
  let s := SSet.opObjEquiv η
  let a := fun c => SSet.opObjEquiv.symm (s.val c)
  refine ⟨fun c => (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj c)).hom.app n (a c), ?_⟩
  intro c d f k α x
  have hη : (SSet.opFunctor.map ((ihom (F.obj c)).map (G.map f))).app n (a c) =
      (SSet.opFunctor.map ((pre (F.map f)).app (G.obj d))).app n (a d) := by
    exact congrArg SSet.opObjEquiv.symm (strictDiagramMappingSimplex_post_pre s f)
  have e : ((ihom (F.obj c).op).map (SSet.opFunctor.map (G.map f))).app n
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj c)).hom.app n (a c)) =
      ((pre (SSet.opFunctor.map (F.map f))).app (G.obj d).op).app n
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj d) (G.obj d)).hom.app n (a d)) := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj d)).hom.app n
          ((SSet.opFunctor.map ((ihom (F.obj c)).map (G.map f))).app n (a c)) :=
        (congrArg (fun h => h.app n (a c)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post (F.obj c) (G.map f))).symm
      _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj d)).hom.app n
          ((SSet.opFunctor.map ((pre (F.map f)).app (G.obj d))).app n (a d)) :=
        congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj d)).hom.app n z) hη
      _ = _ := congrArg (fun h => h.app n (a d))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre (F.map f) (G.obj d))
  exact congrArg (fun h => h.app k α x) e

/-- 反転する全変換空間から一成分の反転内部 Hom への実際の評価射。 -/
def strictDiagramOppositeHomComponent {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G).op ⟶ (ihom (F.obj c).op).obj (G.obj c).op :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj c)).hom

/-- 係数反転は strict な全変換空間の間の実際の単体集合の射。 -/
def strictDiagramOppositeHom {C : Type u} [Category.{u} C] (F G : C ⥤ SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace (F ⋙ SSet.opFunctor) (G ⋙ SSet.opFunctor) where
  app n := ↾fun η => ⟨fun c => (strictDiagramOppositeHomComponent F G c).app n η,
    (strictDiagramOppositeHomSimplex F G (n := n) η).property⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro η
    apply Subtype.ext
    funext c
    change (strictDiagramOppositeHomComponent F G c).app e
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G).op.map α η) =
      ((ihom (F.obj c).op).obj (G.obj c).op).map α
        ((strictDiagramOppositeHomComponent F G c).app d η)
    exact congrArg (fun f => f η) ((strictDiagramOppositeHomComponent F G c).naturality α)

/-- 反転後の一成分への評価は、元の評価の反転と同じ内部 Hom の同型の合成。 -/
lemma strictDiagramOppositeHom_component {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramOppositeHom F G ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F ⋙ SSet.opFunctor) (G ⋙ SSet.opFunctor) c =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (F.obj c) (G.obj c)).hom := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
