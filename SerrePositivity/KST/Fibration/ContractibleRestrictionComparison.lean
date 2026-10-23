module
public import SerrePositivity.KST.Fibration.ContractibleTargetRestriction
public import SerrePositivity.InfinityCategories.Core.VertexFiber

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
    (functorVertex f) (functorVertex g)
  invertible : IsInvertibleEdge edge
  restriction : ((pre i).app Z).app (Opposite.op ⦋1⦌) edge.edge =
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj Z))
      (functorVertex (i ≫ f))).edge

/-- 同じ実可逆辺から得る全関手同型。指定部分上の情報は元の edge と restriction が保持。 -/
def FixedRestrictionFunctorEdge.iso {A B Z : SSet.{u}} [Quasicategory Z]
    {i : A ⟶ B} {f g : B ⟶ Z} (E : FixedRestrictionFunctorEdge i f g) : FunctorIso f g := by
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
    (i : A ⟶ B) [Mono i] (hZ : IsContractibleKan Z) (f g : B ⟶ Z)
    (hfg : i ≫ f = i ≫ g) : FixedRestrictionFunctorEdge i f g := by
  let q := (pre i).app Z
  letI contractibleRestrictionFibration : TrivialKanFibration q :=
    contractibleTargetRestriction_trivialKanFibration i hZ
  let z := q.app (Opposite.op ⦋0⦌) (functorVertex f)
  have hgz : q.app (Opposite.op ⦋0⦌) (functorVertex g) = z := by
    change functorVertex (i ≫ g) = functorVertex (i ≫ f)
    exact congrArg functorVertex hfg.symm
  let v₀ : (vertexFiber q z) _⦋0⦌ := ⟨functorVertex f, by rw [pinchedConstant_zero]⟩
  let v₁ : (vertexFiber q z) _⦋0⦌ :=
    ⟨functorVertex g, by rw [pinchedConstant_zero]; exact hgz⟩
  have hc := vertexFiber_isContractibleKan q z
  letI contractibleRestrictionFiberKan : KanComplex (vertexFiber q z) := hc.kanComplex
  let e := Classical.choice ((hc.isTerminalVertex v₁).nonempty_edge v₀)
  have he : IsInvertibleEdge e :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  refine ⟨e.map ((truncation 2).map (vertexFiberι q z)), he.map _, ?_⟩
  change (vertexFiberι q z ≫ q).app (Opposite.op ⦋1⦌) e.edge = _
  rw [vertexFiberι_comp]
  rfl

end SerrePositivity.KST.Fibration
