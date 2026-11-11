module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：頂点と関手の同型を単体順序の反転へ移す。
方針：同型の辺の代表を反転し、内部 Hom の標準反転同型で写す。
規約：標的の quasicategory 性だけを要求し、Kan 性へ強めない。
使われ方：Hom の族から回収した反変表示の復元同型を元の全空間へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 頂点の同型は反転した単体集合の同じ二頂点の同型へ移る。 -/
def VertexIso.op {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := X.op) (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y e.hom).choose
  have ha : SSet.Truncated.HomotopyCategory.homMk a = e.hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y e.hom).choose_spec
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  haveI := hi.op
  exact (asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a))).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.VertexIso (op)


/-- 内部 Hom の標準反転同型は、関手頂点を同じ射の反転の関手頂点に写す。 -/
lemma oppositeInternalHomIso_vertex {X Y : SSet.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map f) := by
  have h : SSet.opFunctor.map (curry' f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom =
      curry' (SSet.opFunctor.map f) := by
    apply uncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHom_map_uncurry]
    simp only [curry', uncurry_curry, Functor.map_comp, ← Category.assoc]
    rfl
  exact congrArg (fun k => k.app (Opposite.op ⦋0⦌) PUnit.unit) h

/-- 関手同型は同じ二つの射の反転の間の関手同型へ移る。 -/
def FunctorIso.op {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.opFunctor.map f) (SSet.opFunctor.map g) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (VertexIso.op e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom
  rw [oppositeInternalHomIso_vertex, oppositeInternalHomIso_vertex] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.FunctorIso (op)


/-- 反転した同じ二射の関手同型は、二重反転の標準同型で元へ戻せる。 -/
def FunctorIso.unop {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.opFunctor.map f) (SSet.opFunctor.map g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  have h := (e.op.precomp (SSet.opFunctorCompOpFunctorIso.app X).inv).postcomp
    (SSet.opFunctorCompOpFunctorIso.app Y).hom
  have hf : (SSet.opFunctorCompOpFunctorIso.app X).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map f) ≫
        (SSet.opFunctorCompOpFunctorIso.app Y).hom = f := by
    calc
      _ = (SSet.opFunctorCompOpFunctorIso.app X).inv ≫
          (SSet.opFunctorCompOpFunctorIso.app X).hom ≫ f :=
        congrArg (fun k => (SSet.opFunctorCompOpFunctorIso.app X).inv ≫ k)
          (SSet.opFunctorCompOpFunctorIso.hom.naturality f)
      _ = f := Iso.inv_hom_id_assoc _ _
  have hg : (SSet.opFunctorCompOpFunctorIso.app X).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map g) ≫
        (SSet.opFunctorCompOpFunctorIso.app Y).hom = g := by
    calc
      _ = (SSet.opFunctorCompOpFunctorIso.app X).inv ≫
          (SSet.opFunctorCompOpFunctorIso.app X).hom ≫ g :=
        congrArg (fun k => (SSet.opFunctorCompOpFunctorIso.app X).inv ≫ k)
          (SSet.opFunctorCompOpFunctorIso.hom.naturality g)
      _ = g := Iso.inv_hom_id_assoc _ _
  simpa only [Category.assoc, hf, hg] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.FunctorIso (unop)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
