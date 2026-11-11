module
public import SerrePositivity.KST.Fibration.ContractibleTargetRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-! # 可縮な実標的で、指定した部分族の上で恒等となる全関手の可逆辺 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の全関手族を結び、指定部分への制限が同じ恒等一単体である可逆辺。 -/
structure FixedRestrictionFunctorEdge {A B Z : SSet.{u}} [Quasicategory Z]
    (i : A ⟶ B) (f g : B ⟶ Z) where
  edge : Truncated.Edge (X := (truncation 2).obj ((ihom B).obj Z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
  invertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge edge
  restriction : ((pre i).app Z).app (Opposite.op ⦋1⦌) edge.edge =
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f))).edge

/-- 同じ実可逆辺から得る全関手同型。指定部分上の情報は元の edge と restriction が保持。 -/
def FixedRestrictionFunctorEdge.iso {A B Z : SSet.{u}} [Quasicategory Z]
    {i : A ⟶ B} {f g : B ⟶ Z} (E : FixedRestrictionFunctorEdge i f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  letI fixedRestrictionEdgeIso : IsIso (Truncated.HomotopyCategory.homMk E.edge) := E.invertible
  exact asIso (Truncated.HomotopyCategory.homMk E.edge)

/-- 元の比較辺の全後合成は、指定部分上の同じ恒等一単体を保つ。 -/
def FixedRestrictionFunctorEdge.postcomp {A B Z W : SSet.{u}}
    [Quasicategory Z] [Quasicategory W] {i : A ⟶ B} {f g : B ⟶ Z}
    (E : FixedRestrictionFunctorEdge i f g) (j : Z ⟶ W) :
    FixedRestrictionFunctorEdge i (f ≫ j) (g ≫ j) where
  edge := E.edge.map ((truncation 2).map ((ihom B).map j))
  invertible := E.invertible.map _
  restriction := by
    have hn := congrArg (fun h => h.app (Opposite.op ⦋1⦌) E.edge.edge)
      ((pre i).naturality j)
    have he := congrArg (fun t => ((ihom A).map j).app (Opposite.op ⦋1⦌) t) E.restriction
    exact hn.trans he

/-- 同じ指定部分族を持つ二つの実関手を、実制限 fiber の中の可逆辺で結ぶ。 -/
def contractibleRestrictionComparison {A B Z : SSet.{u}} [Quasicategory Z]
    (i : A ⟶ B) [Mono i] (hZ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Z) (f g : B ⟶ Z)
    (hfg : i ≫ f = i ≫ g) : FixedRestrictionFunctorEdge i f g := by
  let q := (pre i).app Z
  letI contractibleRestrictionFibration : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q :=
    contractibleTargetRestriction_trivialKanFibration i hZ
  let z := q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  have hgz : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) = z := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f)
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hfg.symm
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) _⦋0⦌ :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact hgz⟩
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan q z
  letI contractibleRestrictionFiberKan : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) := hc.kanComplex
  let e := Classical.choice ((hc.isTerminalVertex v₁).nonempty_edge v₀)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  refine ⟨e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q z)), he.map _, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q z ≫ q).app (Opposite.op ⦋1⦌) e.edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
  rfl

end SerrePositivity.KST.Fibration
