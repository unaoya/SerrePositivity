module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramBoundaryNaturality
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramVertexEvaluation
public import SerrePositivity.KST.LocalizingInvariants.SpectrumPiZero
public import SerrePositivity.KST.Spectra.SpectrumNativeLoopCircleIso

/-!
概要：元の loop 四角形の全族のホモトピー圏を、実 fiber 図式の圏へ送る。
方針：元の関手圏への包含を、四角形の復号の同型で輸送する。
規約：任意の図式間の射を扱い、四辺だけの可換式へ置き換えない。
使われ方：native loop の整数 π の次数移動の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumLoop

abbrev diagrams := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u}

def fiberDiagramAt (x : diagrams.{u} _⦋0⦌) : FiberDiagram.{u} where
  triangle := ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram x.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x).1⟩
  isFiber := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x).2.2

def inclusion : diagrams.{u} ⟶ ((ihom ((Δ[1] : SSet.{u+1}) ⊗ Δ[1])).obj Sp.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι

def diagramIso (x : hoFunctor.obj diagrams.{u}) :
    FiberDiagram.diagramVertex (fiberDiagramAt x.as.as) ≅ (hoFunctor.map inclusion).toFunctor.obj x :=
  eqToIso (congrArg HomotopyCategory.mk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply x.as.as.val))

def fiberDiagramMap {x y : hoFunctor.obj diagrams.{u}} (f : x ⟶ y) :
    fiberDiagramAt x.as.as ⟶ fiberDiagramAt y.as.as := by
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (fiberDiagramAt x.as.as).triangle.square
    (fiberDiagramAt y.as.as).triangle.square
  exact (diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map f ≫ (diagramIso y).inv

def fiberDiagrams : hoFunctor.obj diagrams.{u} ⥤ FiberDiagram.{u} where
  obj x := fiberDiagramAt x.as.as
  map := fiberDiagramMap
  map_id x := by
    change (diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map (𝟙 x) ≫
      (diagramIso x).inv = 𝟙 _
    exact (congrArg (fun a => (diagramIso x).hom ≫ a ≫ (diagramIso x).inv)
      ((hoFunctor.map inclusion).toFunctor.map_id x)).trans
        ((congrArg ((diagramIso x).hom ≫ ·) (Category.id_comp (diagramIso x).inv)).trans
          (diagramIso x).hom_inv_id)
  map_comp {x y z} f g := by
    change (diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map (f ≫ g) ≫
      (diagramIso z).inv =
        ((diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map f ≫ (diagramIso y).inv) ≫
          ((diagramIso y).hom ≫ (hoFunctor.map inclusion).toFunctor.map g ≫ (diagramIso z).inv)
    have hm := congrArg (fun a => (diagramIso x).hom ≫ a ≫ (diagramIso z).inv)
      ((hoFunctor.map inclusion).toFunctor.map_comp f g)
    apply hm.trans
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

def diagramInclusionIso : fiberDiagrams.{u} ⋙ FiberDiagram.diagramInclusion ≅
    (hoFunctor.map inclusion).toFunctor :=
  NatIso.ofComponents (fun x => by
    change FiberDiagram.diagramVertex (fiberDiagramAt x.as.as) ≅ _
    exact diagramIso x) (by
    intro x y f
    change ((diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map f ≫
      (diagramIso y).inv) ≫ (diagramIso y).hom =
        (diagramIso x).hom ≫ (hoFunctor.map inclusion).toFunctor.map f
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

def vertexIso (i j : Fin 2) :
    fiberDiagrams.{u} ⋙ FiberDiagram.vertex i j ≅
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} i j)).toFunctor := by
  let ev := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (X := (Δ[1] : SSet.{u+1}) ⊗ Δ[1]) (Y := Sp.{u})
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor
  have he : (hoFunctor.map inclusion).toFunctor ⋙ ev =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} i j)).toFunctor := by
    change (hoFunctor.map inclusion ≫ hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (Δ[1] : SSet.{u+1}) ⊗ Δ[1]) (Y := Sp.{u})
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))).toFunctor = _
    rw [← Functor.map_comp]
    rfl
  exact Functor.isoWhiskerLeft fiberDiagrams (FiberDiagram.vertexEvaluationIso i j).symm ≪≫
    (Functor.associator fiberDiagrams FiberDiagram.diagramInclusion ev).symm ≪≫
      (Functor.isoWhiskerRight diagramInclusionIso ev) ≪≫ eqToIso he

end SerrePositivity.KST.LocalizingInvariants.SpectrumLoop
