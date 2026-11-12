module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeVertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：同じ底上の right fibrations の元の比較射を、全ての指定 fiber 上で同値と判定する。
方針：fiber の標準反転同型の自然性で left 側の証明済み判定へ移し、二重反転で元の射へ戻す。
規約：元の比較射を固定し、全体の同値性を追加仮定にしない。
使われ方：小さい元の圏から Yoneda comma への元の比較の同値性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 元の底上の比較の反転は、同じ fiber 比較の反転と標準同型で厳密に可換。 -/
lemma oppositeVertexFiberMap_naturality {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (SSet.opFunctor.map p) (SSet.opFunctor.map q) (SSet.opFunctor.map f)
        (by rw [← Functor.map_comp, hf]) (SSet.opObjEquiv.symm b) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso q b).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  rfl

/-- 指定写像の反転が同値なら、同じ元の写像も同値。 -/
lemma isQCatEquivalence_of_opposite_map {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (SSet.opFunctor.map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj X) :=
    inferInstanceAs (Quasicategory X.op.op)
  have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj Y) :=
    inferInstanceAs (Quasicategory Y.op.op)
  have : Quasicategory ((𝟭 SSet.{u}).obj X) := inferInstanceAs (Quasicategory X)
  have : Quasicategory ((𝟭 SSet.{u}).obj Y) := inferInstanceAs (Quasicategory Y)
  have h := hf.opposite.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app Y)).isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((SSet.opFunctor ⋙ SSet.opFunctor).map f ≫
    (SSet.opFunctorCompOpFunctorIso.app Y).hom) at h
  have hn : (SSet.opFunctor ⋙ SSet.opFunctor).map f ≫
      (SSet.opFunctorCompOpFunctorIso.app Y).hom =
      (SSet.opFunctorCompOpFunctorIso.app X).hom ≫ f :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctorCompOpFunctorIso.app X)).isQCatEquivalence.cancel_left
    (Eq.mp (congrArg (fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) hn) h)

/-- 元の right fibration 間の比較射は、全指定 fiber で同値なら元の全空間で同値。 -/
lemma isQCatEquivalence_of_rightFibration_fibers {E E' B : SSet.{u}}
    [Quasicategory E] [Quasicategory E'] [Quasicategory B]
    (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : Quasicategory E' := quasicategory_of_innerFibration q
  apply isQCatEquivalence_of_opposite_map f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers
    (SSet.opFunctor.map p) (SSet.opFunctor.map q) (SSet.opFunctor.map f)
    (by rw [← Functor.map_comp, hf])
  intro b'
  obtain ⟨b, rfl⟩ := (SSet.opObjEquiv (X := B) (n := Opposite.op ⦋0⦌)).symm.surjective b'
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso p b)).isQCatEquivalence.cancel_left
  exact Eq.mpr (congrArg (fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g)
    (oppositeVertexFiberMap_naturality p q f hf b))
      ((h b).opposite.comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso q b)).isQCatEquivalence)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
