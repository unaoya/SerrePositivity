module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompStructCocone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IteratedSliceUnderRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction

/-!
概要：元の全余錐を恒等長辺に持つ分裂三角形から、二つの頂点を加えた全余錐を作る。
方針：coslice 内の三角形余錐を反復 coslice 同型で元の圏へ展開する。
規約：元の増大余錐と新しい表示段を全 join 図式として保持する。
使われ方：可算交互図式の有限段階の増大余錐の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {L C : SSet.{u}} {F : L ⟶ C} {c d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋0⦌}
  {e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge c d} {r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge d c}

/-- 概要：余錐間の分裂三角形を元の全交互図式の余錐に展開する。
方針：三角形を最初の辺の余錐に読み替え、反復 coslice 同型を適用する。
規約：元の三角形を選び直さない。
使われ方：次の二頂点を加えた増大図式。 -/
def splitCoconeExtension (T : e.CompStruct r (SSet.Edge.id c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso (SSet.yonedaEquiv.symm e.edge)).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone T)

/-- 概要：拡張した全余錐の頂点は元の増大余錐の頂点。
方針：反復同型の二重射影と元の三角形余錐の頂点を計算する。
規約：元の標的頂点を厳密に保つ。
使われ方：交互段の固定 fiber 頂点の整合。 -/
lemma splitCoconeExtension_vertex (T : e.CompStruct r (SSet.Edge.id c)) :
    (splitCoconeExtension T).vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋0⦌) c := by
  let q := SSet.yonedaEquiv.symm e.edge
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone T
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso_projection q)
  change (splitCoconeExtension T).vertex =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋0⦌) z.vertex at h
  dsimp only [z] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone_vertex] at h
  exact h

/-- 概要：拡張した全余錐の元の図式への制限は元の増大余錐そのもの。
方針：反復同型の左因子制限を同じ三角形余錐に適用する。
規約：全余錐値の等式であり、脚だけの比較ではない。
使われ方：可算図式の既存段階を保持する。 -/
lemma splitCoconeExtension_old_val (T : e.CompStruct r (SSet.Edge.id c)) :
    ((splitCoconeExtension T).restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L Δ[1])).val = c.val := by
  let q := SSet.yonedaEquiv.symm e.edge
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone T
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) z)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso_restriction q)
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction q).app (Opposite.op ⦋0⦌)
    (splitCoconeExtension T) = z.vertex at h
  dsimp only [z] at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone_vertex] at h
  have hv := congrArg Subtype.val h
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed q))).hom.app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L Δ[1])).app
      (Opposite.op ⦋0⦌) (splitCoconeExtension T))).val = c.val at hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed q)] at hv
  exact hv

/-- 概要：次の全図式の最初の新頂点への制限も、元の増大余錐全体。
方針：最初の辺の始点と uncurry の前合成を使う。
規約：元の余錐を全射の等式で保持する。
使われ方：挿入される固定標的の頂点と前段の整合。 -/
lemma splitCoconeExtension_first_val :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 L) (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge) = c.val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, e.δ_one_yonedaEquiv_symm]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda 0 c

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
