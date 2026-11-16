module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofEndpointTransport

/-! 同じprobe射の二つの宇宙表示と、元のroofの指定probe同型の類を照合する。 -/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
attribute [local instance] jointRoofEndpointTransportModel jointRoofEndpointTransportFactorization
/-- 同じ元のprobe射とモデル源の既存表示・指定頂点同型の係数移送則。 -/
lemma strictBETotModelSource_edge {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (((nerve.edgeMk ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map f)).map
      (strictBETotModelSource A)).edge) =
      (((nerve.edgeMk f).map (algebraCAlgSource A)).edge) := by
  change (cAlgLocalizationSource A).app (Opposite.op ⦋1⦌) _ =
    (cAlgLocalizationSource A).app (Opposite.op ⦋1⦌) _
  apply congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋1⦌))
  exact ComposableArrows.ext₁ rfl rfl (by rfl)
/-- 同じ元のprobe射とモデル源の既存表示・指定頂点同型の係数移送則。 -/
lemma strictBETotJointRoofProbeEndpointIso_hom_arrow (P : strictBETotJointHomIndex A) :
    Arrow.mk (strictBETotJointRoofProbeEndpointIso A P).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (framedLimitProbeComparison A (AsSmall.down.obj P).1.unop))).map
        (strictBETotModelSource A))) := by
  unfold strictBETotJointRoofProbeEndpointIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    ← Category.assoc, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
  rw [strictBETotProbeSourceIso_hom]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact (strictBETotModelSource_edge A (framedLimitProbeComparison A (AsSmall.down.obj P).1.unop)).symm

end SerrePositivity.EInfinity.BarrattEccles
end
