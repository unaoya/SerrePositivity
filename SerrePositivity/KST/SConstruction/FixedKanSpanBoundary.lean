module
public import SerrePositivity.KST.SConstruction.RelativeKanSpanFamilies
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 定数な二円柱の境界からの指定逆・合成三角形
概要：境界で定数な二円柱に、恒等合成辺を持つ実際の span 三角形を供給する。
方針：実円柱の定数性から制限した関手辺の恒等性を読み、退化二単体で三角形を作る。
規約：境界三角形の存在を追加仮定とせず、元の制限辺を厳密に保持する。
使われ方：元の Path 合成面で固定する二円柱を BF の相対厳密化へ接続する。
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

/-- 境界での実円柱の定数性は、制限した元の関手辺の恒等性を与える。 -/
lemma fixedHomotopySpanEdge {T U E : SSet.{u}} (j : T ⟶ U) {D F : U ⟶ E}
    (a : SSet.Homotopy D F)
    (ha : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = fst T Δ[1] ≫ j ≫ D) :
    ((pre j).app E).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a).edge =
      (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ D))).edge := by
  apply SSet.yonedaEquiv.symm.injective
  apply uncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, uncurry_pre_app]
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (curry a.h) = _
  rw [uncurry_curry, ha]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

/-- 二辺が元の恒等辺なら、指定した逆・合成三角形と恒等合成辺を退化から作る。 -/
def fixedKanSpanTriangleData {E : SSet.{u}} {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y)
    (ha : a.edge = (SSet.Edge.id z).edge) (hb : b.edge = (SSet.Edge.id z).edge) :
    {t : KanSpanTriangleData a b // t.edge.edge = (SSet.Edge.id x).edge} := by
  have hx : x = z := a.tgt_eq.symm.trans
    ((congrArg (E.δ (0 : Fin 2)) ha).trans (SSet.Edge.id z).tgt_eq)
  have hy : y = z := b.tgt_eq.symm.trans
    ((congrArg (E.δ (0 : Fin 2)) hb).trans (SSet.Edge.id z).tgt_eq)
  subst x
  subst y
  have hea : a = SSet.Edge.id z := SSet.Edge.ext ha
  have heb : b = SSet.Edge.id z := SSet.Edge.ext hb
  subst a
  subst b
  exact ⟨⟨SSet.Edge.id z, SSet.Edge.CompStruct.idCompId z,
    SSet.Edge.id z, SSet.Edge.CompStruct.idCompId z⟩, rfl⟩

/-- 元の境界で定数な二円柱には、恒等合成辺を持つ指定境界三角形を構成できる。 -/
def fixedKanHomotopySpanBoundary {T U E : SSet.{u}} (j : T ⟶ U)
    {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (ha : (j ▷ (Δ[1] : SSet.{u})) ≫ a.h = fst T Δ[1] ≫ j ≫ D)
    (hb : (j ▷ (Δ[1] : SSet.{u})) ≫ b.h = fst T Δ[1] ≫ j ≫ D) :
    {t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E)) //
      t.edge.edge = (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F))).edge} :=
  fixedKanSpanTriangleData _ _ (fixedHomotopySpanEdge j a ha) (fixedHomotopySpanEdge j b hb)

/-- 定数境界の実円柱を更に制限しても、同じ元の始点の像で全時刻固定する。 -/
lemma fixedHomotopySpanBoundary_precomp {K T U E : SSet.{u}}
    (i : K ⟶ T) (j : T ⟶ U) {D F : U ⟶ E} (H : SSet.Homotopy D F)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst T Δ[1] ≫ j ≫ D) :
    ((i ≫ j) ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ (i ≫ j) ≫ D := by
  rw [comp_whiskerRight_assoc, h, whiskerRight_fst_assoc, Category.assoc]

/-- 境界で元の始点を固定する円柱の終点も、同じ始点の族を厳密に回収する。 -/
lemma fixedHomotopySpanBoundary_target {T U E : SSet.{u}} (j : T ⟶ U)
    {D F : U ⟶ E} (H : SSet.Homotopy D F)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst T Δ[1] ≫ j ≫ D) :
    j ≫ F = j ≫ D := by
  have hh := congrArg (fun m => SSet.ι₁ ≫ m) h
  rw [SSet.ι₁_comp_assoc, H.h₁] at hh
  simpa only [← Category.assoc, SSet.ι₁_fst, Category.id_comp] using hh

end SerrePositivity.KST.SConstruction
