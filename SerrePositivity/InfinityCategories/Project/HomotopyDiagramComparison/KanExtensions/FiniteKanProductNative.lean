module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.FiniteSSetProductUniversal
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg

/-!
概要：元の有限非空 Kan 族の反復積を頂点とする native な積錐。
方針：元の全射影の通常の積錐を作り、元の台の極限性から coherent nerve へ移す。
規約：頂点は元の反復積そのもの。添字だけを元の小さい宇宙へ持ち上げる。
使われ方：sifted な底上の元の全空間 Kan 比較による有限積錐の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の有限非空 Kan 族を、持ち上げた有限離散添字の通常の図式にする。 -/
def finiteKanProductDiagram (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    Discrete (ULift.{u} (Fin (n + 1))) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Discrete.functor (fun i ↦ E i.down)

/-- 元の Kan 族の台の反復積を、同じ Kan 対象に束ねる。 -/
def finiteKanProductObject (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ (E i).obj),
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_kanComplex n _ (fun _ ↦ inferInstance)⟩

/-- 元の反復積と元の全射影の通常の錐。 -/
def finiteKanProductCone (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    Cone (finiteKanProductDiagram n E) where
  pt := finiteKanProductObject n E
  π := Discrete.natTrans (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ (E j).obj) i.as.down)

/-- 元の通常の全射影の錐は、台の単体集合の積錐。 -/
def finiteKanProductCone_forget_isLimit (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (finiteKanProductCone n E)) where
  lift s := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift n (fun i ↦ s.π.app (Discrete.mk (ULift.up i)))
  fac s i := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection n _ i.as.down
  uniq s f hf := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_hom_ext n _ (fun i ↦ by
    exact (hf (Discrete.mk (ULift.up i))).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection n
        (E := fun j ↦ (E j).obj) (fun j ↦ s.π.app (Discrete.mk (ULift.up j))) i).symm)

/-- 元の反復積を頂点とする有限非空 Kan 図式の native な全錐。 -/
def finiteKanProductNativeCone (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (finiteKanProductDiagram n E)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (finiteKanProductCone n E)).cast
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram (finiteKanProductDiagram n E))

/-- 元の finite 積錐の頂点は元の反復積 Kan 対象の標準頂点そのもの。 -/
lemma finiteKanProductNativeCone_vertex (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (finiteKanProductNativeCone n E).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (finiteKanProductObject n E) := by
  rw [finiteKanProductNativeCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  rfl

/-- 元の反復積を頂点とする全錐は、実際の native な有限非空積錐。 -/
lemma finiteKanProductNativeCone_isLimit (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteKanProductNativeCone n E) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit (finiteKanProductCone n E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (finiteKanProductCone_forget_isLimit n E))

/-- 元の有限積錐の native な全脚は、元の通常の射影の全一単体。 -/
lemma finiteKanProductNativeCone_leg_edge (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (finiteKanProductNativeCone n E)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((finiteKanProductCone n E).π.app i)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (finiteKanProductCone n E) i

/-- 元の有限積錐の native な脚を戻すと、元の通常の射影そのもの。 -/
lemma finiteKanProductNativeCone_kanLeg (n : ℕ) (E : Fin (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (finiteKanProductNativeCone n E) (finiteKanProductObject n E)
      (finiteKanProductNativeCone_vertex n E) i = (finiteKanProductCone n E).π.app i := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLegEdge (finiteKanProductNativeCone n E) (finiteKanProductObject n E)
      (finiteKanProductNativeCone_vertex n E) i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((finiteKanProductCone n E).π.app i) := by
    apply SSet.Edge.ext
    exact finiteKanProductNativeCone_leg_edge n E i
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge _)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
