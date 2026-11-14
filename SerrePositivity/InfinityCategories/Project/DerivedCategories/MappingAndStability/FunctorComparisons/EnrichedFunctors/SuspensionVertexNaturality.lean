module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.SuspensionSquareHomComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionAmbientHom

/-! # 標準 suspension 頂点と懸垂関手の自然な比較

概要：Semifree の標準 cone 頂点は、h D(S) の懸垂関手の値と鎖写像に対して自然に同型。
方針：実際の四角形比較の両端成分を指定し、懸垂の普遍性による自然性を使う。
規約：複体シフトとの比較は後続。使われ方：D7 の D3 による suspension 比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- Semifree の比較の始点成分を指定した Hom の等式で表す。 -/
lemma semifreeSuspensionSquareHom_source (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) 0 0).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a) =
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).source_eq) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a) ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).source_eq.symm) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom_source_arrow a)
  exact hf

/-- Semifree の比較の終点成分を指定した Hom の等式で表す。 -/
lemma semifreeSuspensionSquareHom_target (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) 1 1).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a) =
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X)) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X))
            (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)) ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex Y).symm) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom_target_arrow a)
  exact hf

/-- 選択された懸垂から標準 cone 頂点への同型。 -/
def semifreeSuspensionVertexIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) ≅
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X))

/-- 標準 suspension 頂点と懸垂関手の比較は鎖写像に対して自然。 -/
lemma semifreeSuspensionVertexIso_naturality (a : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).map
        (SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a)) ≫
      (semifreeSuspensionVertexIso Y).hom =
    (semifreeSuspensionVertexIso X).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X))
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).ambientHom_target (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a)
    (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) a))
    (semifreeSuspensionSquareHom_source a)
  rw [semifreeSuspensionSquareHom_target] at h
  have hh := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso.hom ≫ z ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).suspensionFunctorObjIso.hom ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex Y))) h
  simpa only [semifreeSuspensionVertexIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp] using hh.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
