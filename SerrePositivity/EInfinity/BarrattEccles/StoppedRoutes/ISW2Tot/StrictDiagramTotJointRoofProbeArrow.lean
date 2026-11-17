module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofEndpointTransport

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。 同じprobe射の二つの宇宙表示と、元のroofの指定probe同型の類を照合する。 -/

@[expose] public section
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointRoofEndpointTransportModel _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointRoofEndpointTransportFactorization
/-- 同じ元のprobe射とモデル源の既存表示・指定頂点同型の係数移送則。 -/
lemma strictBETotModelSource_edge {X Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : X ⟶ Y) :
    (((nerve.edgeMk ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map f)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).edge) =
      (((nerve.edgeMk f).map (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A)).edge) := by
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋1⦌) _ =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋1⦌) _
  apply congrArg ((_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app (Opposite.op ⦋1⦌))
  exact ComposableArrows.ext₁ rfl rfl (by rfl)
/-- 同じ元のprobe射とモデル源の既存表示・指定頂点同型の係数移送則。 -/
lemma strictBETotJointRoofProbeEndpointIso_hom_arrow (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    Arrow.mk (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofProbeEndpointIso A P).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj P).1.unop))).map
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  unfold _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofProbeEndpointIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    ← Category.assoc, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso_hom]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_edge A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj P).1.unop)).symm

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
end
