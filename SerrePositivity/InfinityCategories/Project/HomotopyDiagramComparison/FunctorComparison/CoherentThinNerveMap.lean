module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：単体的圏から薄い通常の圏への関手を、coherent nerve の全次数の射へ延長する。
方針：元の対象・辺から二次切断上の射を作り、nerve の二余骨格性で延長する。
規約：豊穣関手性や局所 Kan 性を入力しない。使われ方：cf 対応圏の区間射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplexCategory.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {E : Type (max u v)} [Category.{max u v} E] [Quiver.IsThin E] (P : C ⥤ E)

/-- coherent nerve の任意の両端頂点を元の対象へ戻した通常の射。 -/
def coherentEdgeObjectHom {x y : (SimplicialNerve C) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (SimplicialNerve C)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom
    ⟨e.edge, e.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x).symm,
      e.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y).symm⟩

/-- 通常の薄い標的への関手は、coherent nerve のホモトピー圏からの関手を与える。 -/
def coherentThinHoFunctor : hoFunctor.obj (SimplicialNerve C) ⥤ E :=
  SSet.Truncated.HomotopyCategory.lift (fun x ↦ P.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x))
    (fun e ↦ P.map (coherentEdgeObjectHom e))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)

/-- 二次切断の辺の作用を標的 nerve の二余骨格で延長した、全次数の射。 -/
def coherentThinNerveMap : SimplicialNerve C ⟶ nerve E :=
  (coskAdj 2).homEquiv (SimplicialNerve C) ((truncation 2).obj (nerve E))
    (Truncated.HomotopyCategory.homToNerveMk (coherentThinHoFunctor P)) ≫
      Nerve.cosk₂Iso.inv.app (Cat.of E)

/-- 延長した射の二次切断は、元の対象と辺から作った射に厳密に一致する。 -/
lemma coherentThinNerveMap_truncation :
    (truncation 2).map (coherentThinNerveMap P) =
      Truncated.HomotopyCategory.homToNerveMk (coherentThinHoFunctor P) := by
  apply ((coskAdj 2).homEquiv (SimplicialNerve C) _).injective
  rw [Adjunction.homEquiv_apply]
  change (coskAdj 2).unit.app (SimplicialNerve C) ≫
    (truncation 2 ⋙ Truncated.cosk 2).map (coherentThinNerveMap P) = _
  rw [← (coskAdj 2).unit.naturality]
  change (((coskAdj 2).homEquiv _ _
    (Truncated.HomotopyCategory.homToNerveMk (coherentThinHoFunctor P))) ≫
      Nerve.cosk₂Iso.inv.app (Cat.of E)) ≫ Nerve.cosk₂Iso.hom.app (Cat.of E) = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- 延長した射は、元の通常の関手と同じ対象を零単体の像に持つ。 -/
lemma coherentThinNerveMap_vertex (X : C) :
    (coherentThinNerveMap P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (P.obj X) := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))
    (coherentThinNerveMap_truncation P)
  exact h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
