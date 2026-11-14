module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCocones

/-!
概要：通常の strict 図式の coherent 表示は反対の標準同型と厳密に可換。
方針：各単体の通常の射列を反転し、coherent な Hom の定値単体を比較する。
規約：対象と Hom の二宇宙を区別し、持ち上げた添字の反転の同型を明示する。
使われ方：HTT 4.2.4.1、双対化した余錐の図式を元の標準図式と同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：strict な図式の coherent 表示は単体集合と圏の反対の標準比較と厳密に可換。
方針：元の射列の反転を定値な豊穣 Hom の反対と比較する。
規約：Kan 性や図式の形状の仮定は不要。
使われ方：余錐の表示の固定図式を元の strict 図式へ戻す。 -/
lemma strictCoherentDiagram_opposite {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve I)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := I)).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F.op := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：双対化から得た通常の余錐の固定図式は元の標準の strict 図式に厳密に等しい。
方針：通常の図式の反対の可換式を逆の同型で戻し、二重反転の自然性を使う。
規約：頂点や辺だけでなく全ての単体の等式として述べる。
使われ方：native な余錐を元の既存の図式上へ移送する。 -/
lemma strictCoherentCoconeDiagram_eq {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCoconeDiagram F = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve I)).inv ≫
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := I)).hom
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C
  have h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F.op ≫ e.inv =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) := by
    have ho : SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) ≫ e.hom =
        a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F.op := by
      simpa only [a, e, Category.assoc] using strictCoherentDiagram_opposite F
    rw [← Category.assoc, ← ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) ≫
      (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom =
    (SSet.opFunctorCompOpFunctorIso.app
      ((SSet.uliftFunctor.{v, u}).obj (nerve I))).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCoconeDiagram F =
        (SSet.opFunctorCompOpFunctorIso.app
          ((SSet.uliftFunctor.{v, u}).obj (nerve I))).inv ≫
          SSet.opFunctor.map (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F.op ≫ e.inv) ≫
            (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom := by
      simp only [a, e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCoconeDiagram, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso_hom_factorization,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
        Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
      rw [h, hn, Iso.inv_hom_id_assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
