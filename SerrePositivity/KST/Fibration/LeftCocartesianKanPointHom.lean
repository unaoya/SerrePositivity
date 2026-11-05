module
public import SerrePositivity.KST.Fibration.KanCompletionPointHom

/-! # 元の cocartesian section 比較の指定成分が、同じ包含の係数点を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

/-- 元の cocartesian section 比較の同じ成分を、元の標準 Kan 値で表示する。 -/
def leftCocartesianKanComparisonValueIso (i : I) :
    VertexIso (spaceInfinityVertex ((cocartesianKanDiagram p).obj i))
      (spaceInfinityVertex ((leftStrictTransportFunctor p).obj i)) :=
  _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso (F := cocartesianKanDiagram p) (G := leftStrictTransportFunctor p)
    (leftCocartesianKanComparisonIso p) i

/-- 同じ指定成分は、元の置換単位上で、元の section 包含の点の像を回収する。 -/
theorem leftCocartesianKanComparisonValueIso_pointHom (i : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((cocartesianKanDiagram p).obj i)).symm
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v)) ≫
      (leftCocartesianKanComparisonValueIso p i).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
      ((pointedSpaceFiberVertexEquiv ((leftStrictTransportFunctor p).obj i)).symm
        (((cocartesianStrictTransportInclusion p).app i).app (Opposite.op ⦋0⦌) v)) := by
  let A := cocartesianKanDiagram p
  let B := leftStrictTransportFunctor p
  let G := B ⋙ kanObjectForget ⋙ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion
  let η := Functor.whiskerRight (leftCocartesianKanComparison p) kanObjectForget
  have hη : ∀ c, IsQCatEquivalence (X := (A.obj c).obj) (Y := (G.obj c).obj)
      (η.app c) := by
    intro c
    have := kanCocartesianSectionsι_isIso_of_leftFibration p (nerveMap (Under.forget c))
    apply _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion_map_isQCatEquivalence
    change IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (SerrePositivity.InfinityCategories.cocartesianSectionsι p (nerveMap (Under.forget c))))
    infer_instance
  let e := kanDiagramFunctorIsoOfPointwise
    (F := ⟨A, trivial⟩) (G := ⟨G, trivial⟩) η hη
  let w := ((cocartesianStrictTransportInclusion p).app i).app (Opposite.op ⦋0⦌) v
  let v' := (F2.continuousKanReplacementUnit.app
    ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v
  have he : leftCocartesianKanComparisonValueIso p i =
      _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso e i ≪≫ (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso (kanDiagramCompletionIso B) i).symm := by
    change _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso (e ≪≫ (kanDiagramCompletionIso B).symm) i = _
    rw [_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso_trans, _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso_symm]
  have hw : (η.app i).app (Opposite.op ⦋0⦌) v' =
      (F2.continuousKanReplacementUnit.app (B.obj i).obj).app (Opposite.op ⦋0⦌) w := by
    have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
      (F2.continuousKanReplacementUnit.naturality
        ((cocartesianStrictTransportInclusion p).app i))
    change (F2.continuousKanReplacement.map
      ((cocartesianStrictTransportInclusion p).app i)).app (Opposite.op ⦋0⦌)
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p).obj i)).app (Opposite.op ⦋0⦌) v) =
      (F2.continuousKanReplacementUnit.app ((leftStrictTransportDiagram p).obj i)).app
        (Opposite.op ⦋0⦌)
        (((cocartesianStrictTransportInclusion p).app i).app (Opposite.op ⦋0⦌) v)
    simp only [NatTrans.comp_app_apply, Functor.id_map] at hn
    exact hn.symm
  have hs := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso_pointHom
    (F := ⟨A, trivial⟩) (G := ⟨G, trivial⟩) η hη i v'
  rw [hw] at hs
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramValueIso e i).hom = _ at hs
  have hc := kanDiagramCompletionValueIso_pointHom B i w
  rw [he, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  exact (Iso.comp_inv_eq _).2 (hs.trans hc.symm)

end SerrePositivity.KST.Fibration
