module
public import SerrePositivity.KST.SConstruction.RelativeKanOuterSpanFamilies

/-! # 境界で一致する二円柱の相対合成
概要：二円柱が境界で互いに一致すれば、各円柱の定数性なしに境界固定の合成を作る。
方針：元の境界辺に退化した外側三角形を付け、比較辺を恒等のまま相対持ち上げする。
規約：元の二脚が境界で動くことを許し、境界三角形や逆辺を追加仮定にしない。
使われ方：高次入力の既存境界を保つ BF K の実写像族への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の二脚の raw な辺が同じなら、恒等比較辺と実退化三角形を構成する。 -/
def coincidentKanSpanBoundaryData {E : SSet.{u}} {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) (h : a.edge = b.edge) :
    {e : E.Edge x y // e.edge = (SSet.Edge.id x).edge ∧
      Nonempty (SSet.Edge.CompStruct a e b)} := by
  have hy : y = x := b.tgt_eq.symm.trans
    ((congrArg (E.δ (0 : Fin 2)) h.symm).trans a.tgt_eq)
  subst y
  have hb : b = a := SSet.Edge.ext h.symm
  subst b
  exact ⟨SSet.Edge.id x, rfl, ⟨SSet.Edge.CompStruct.compId a⟩⟩

/-- 境界で同じ実円柱を持つ二辺は、元の関手空間の制限でも raw な辺が等しい。 -/
lemma coincidentKanHomotopySpanEdge {T U E : SSet.{u}} (j : T ⟶ U)
    {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = (j ▷ (Δ[1] : SSet.{u})) ≫ b.h) :
    ((pre j).app E).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a).edge =
      ((pre j).app E).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b).edge := by
  apply SSet.yonedaEquiv.symm.injective
  apply uncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp,
    uncurry_pre_app, uncurry_pre_app]
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (curry a.h) =
    (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (curry b.h)
  simpa only [uncurry_curry] using h

/-- 境界で一致する元の二円柱から、恒等比較辺と退化境界三角形を内部構成する。 -/
def coincidentKanHomotopySpanBoundary {T U E : SSet.{u}} (j : T ⟶ U)
    {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = (j ▷ (Δ[1] : SSet.{u})) ≫ b.h) :
    {e : ((ihom T).obj E).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ G)) //
      e.edge = (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F))).edge ∧
      Nonempty (SSet.Edge.CompStruct
        ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E)) e
        ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E)))} :=
  coincidentKanSpanBoundaryData _ _ (coincidentKanHomotopySpanEdge j a b h)

/-- 元の二円柱が境界で一致する場合の、全パラメータの境界固定相対合成。 -/
def relativeKanCoincidentSpanComposite {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = (j ▷ (Δ[1] : SSet.{u})) ≫ b.h) :
    SSet.Homotopy F G :=
  relativeKanOuterSpanComposite j a b (coincidentKanHomotopySpanBoundary j a b h).val
    (coincidentKanHomotopySpanBoundary j a b h).property.2.some

/-- 元の二円柱は個別に動いても、合成円柱は元の境界を全時刻で厳密に固定する。 -/
lemma relativeKanCoincidentSpanComposite_boundary {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = (j ▷ (Δ[1] : SSet.{u})) ≫ b.h) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeKanCoincidentSpanComposite j a b h).h =
      fst T Δ[1] ≫ j ≫ F :=
  relativeKanOuterSpanComposite_boundary_constant j a b
    (coincidentKanHomotopySpanBoundary j a b h).val
    (coincidentKanHomotopySpanBoundary j a b h).property.2.some
    (coincidentKanHomotopySpanBoundary j a b h).property.1

end SerrePositivity.KST.SConstruction
