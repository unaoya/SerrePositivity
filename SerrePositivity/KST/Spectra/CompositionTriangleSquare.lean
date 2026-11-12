module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTrianglePushout
public import SerrePositivity.KST.Spectra.TriangleDiskFaces
public import SerrePositivity.KST.Spectra.FibrationEdgeComposition

/-!
概要：実合成三角形を、対角辺から第二辺への正方形ホモトピーへ展開する。
方針：元の三角形と対角辺の退化三角形を、同じ対角辺で厳密に貼り合わせる。
規約：標的の Kan 性は不要。使われ方：構造三角形からの区間の構造比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z} (t : SSet.Edge.CompStruct a b c)

/-- 元の三角形と対角辺の退化三角形を貼った、同じ実正方形。 -/
def compositionTriangleSquare : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.desc (SSet.yonedaEquiv.symm t.simplex)
    (SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId c).simplex) (by
      rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
        SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm])

/-- 上側の二単体は、入力した元の三角形単体そのもの。 -/
@[reassoc (attr := simp)]
lemma compositionTriangleSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ compositionTriangleSquare t = SSet.yonedaEquiv.symm t.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inl_desc _ _ _

/-- 下側の二単体は、同じ対角辺の退化三角形。 -/
@[reassoc (attr := simp)]
lemma compositionTriangleSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ compositionTriangleSquare t =
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId c).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inr_desc _ _ _

/-- 正方形の始辺は、元の対角辺そのもの。 -/
lemma compositionTriangleSquare_zero :
    SSet.ι₀ ≫ compositionTriangleSquare t = SSet.yonedaEquiv.symm c.edge := by
  have h : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ _) =
      lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
        (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [h, Category.assoc, SquareTriangles.second_endpoint_one, Category.assoc,
    Category.assoc, compositionTriangleSquare_lower,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm, ← Category.assoc, lift_fst,
    Category.id_comp]

/-- 正方形の終辺は、元の第二辺そのもの。 -/
lemma compositionTriangleSquare_one :
    SSet.ι₁ ≫ compositionTriangleSquare t = SSet.yonedaEquiv.symm b.edge := by
  have h : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ _) =
      lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
        (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [h, Category.assoc, SquareTriangles.second_endpoint_zero, Category.assoc,
    Category.assoc, compositionTriangleSquare_upper,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, ← Category.assoc, lift_fst,
    Category.id_comp]

/-- 始点を動かす辺は、元の第一辺をそのまま保持する。 -/
lemma compositionTriangleSquare_start :
    stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ compositionTriangleSquare t =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a.edge := by
  rw [SquareTriangles.first_endpoint_one, Category.assoc, Category.assoc,
    compositionTriangleSquare_upper, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]

/-- 終点を動かす辺は、同じ終頂点の恒等辺。 -/
lemma compositionTriangleSquare_finish :
    stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) ≫ compositionTriangleSquare t =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (SSet.Edge.id z).edge := by
  rw [SquareTriangles.first_endpoint_zero, Category.assoc, Category.assoc,
    compositionTriangleSquare_lower, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]

/-- 元の三角形の対角辺から第二辺への、同じ正方形による実ホモトピー。 -/
def compositionTriangleHomotopy : SSet.Homotopy (SSet.yonedaEquiv.symm c.edge)
    (SSet.yonedaEquiv.symm b.edge) where
  h := compositionTriangleSquare t
  h₀ := compositionTriangleSquare_zero t
  h₁ := compositionTriangleSquare_one t
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

end SerrePositivity.KST.Spectra
