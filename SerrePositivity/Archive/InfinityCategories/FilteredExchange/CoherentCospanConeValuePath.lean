module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationCospanCone
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalVertexPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：元の cospan 錐の二三角形の可換性を全円柱付きで余極限頂点の値へ移す。
方針：指定可換同型を表す円柱を単位上で厳密に延長し、合成の表示だけ揃える。
規約：元の三角形・指定同型の類・全円柱を保持。使われ方：native な二射影の同時比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：元の二三角形の指定可換同型の全円柱の代表。
方針：同じ指定同型の順方向の射を代表。
規約：元の同型の類を保持。使われ方：Kan 置換後の指定円柱の入力。 -/
def coherentCospanConeTotalPathHomotopy :
    SSet.Homotopy
      (coherentTransformationTotalMap F X C.toLeft ≫ coherentTransformationTotalMap X Z C.fromLeft)
      (coherentTransformationTotalMap F Y C.toRight ≫
        coherentTransformationTotalMap Y Z C.fromRight) :=
  functorHomHomotopy (coherentCospanConeTotalPathIso F X Y Z C).hom

/-- 概要：円柱の辺の類は元の左右三角形からの指定可換同型の射。
方針：代表の選択の仕様。規約：指定した類の等式。使われ方：元の比較の識別。 -/
lemma coherentCospanConeTotalPathHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentCospanConeTotalPathHomotopy F X Y Z C)) =
        (coherentCospanConeTotalPathIso F X Y Z C).hom := functorHomHomotopy_hom _

/-- 概要：元の二三角形の円柱を元の余極限頂点の値の二合成の間へ移す。
方針：指定延長の全円柱を保って両端の合成式だけ輸送。
規約：左右四射は元の頂点射。使われ方：元の cospan 全体の値の指定可換性。 -/
def coherentCospanConeValuePathHomotopy :
    SSet.Homotopy
      (coherentTotalVertexMap F X (coherentTransformationTotalMap F X C.toLeft) ≫
        coherentTotalVertexMap X Z (coherentTransformationTotalMap X Z C.fromLeft))
      (coherentTotalVertexMap F Y (coherentTransformationTotalMap F Y C.toRight) ≫
        coherentTotalVertexMap Y Z (coherentTransformationTotalMap Y Z C.fromRight)) where
  h := (coherentTotalVertexPathHomotopy F Z
    (coherentCospanConeTotalPathHomotopy F X Y Z C)).h
  h₀ := (coherentTotalVertexPathHomotopy F Z
    (coherentCospanConeTotalPathHomotopy F X Y Z C)).h₀.trans
      (coherentTotalVertexMap_comp F X Z _ _)
  h₁ := (coherentTotalVertexPathHomotopy F Z
    (coherentCospanConeTotalPathHomotopy F X Y Z C)).h₁.trans
      (coherentTotalVertexMap_comp F Y Z _ _)
  rel := (coherentTotalVertexPathHomotopy F Z
    (coherentCospanConeTotalPathHomotopy F X Y Z C)).rel

/-- 概要：元の単位上で、値の可換円柱は元の二三角形の指定円柱の像に厳密に制限。
方針：指定 Kan 延長の元の単位上の式。
規約：全単体・全時刻を保持。使われ方：元の可換 path の最終照合。 -/
lemma coherentCospanConeValuePathHomotopy_unit :
    (coherentDiagramTotalUnit F ▷ (Δ[1] : SSet.{u})) ≫
      (coherentCospanConeValuePathHomotopy F X Y Z C).h =
        (coherentCospanConeTotalPathHomotopy F X Y Z C).h ≫ coherentDiagramTotalUnit Z :=
  coherentTotalVertexPathHomotopy_unit F Z (coherentCospanConeTotalPathHomotopy F X Y Z C)

/-- 概要：元の可換円柱が定める値の cospan 錐の指定可換同型。
方針：同じ全円柱の類を使う。規約：代表を変更しない。使われ方：native な射の値比較。 -/
def coherentCospanConeValuePathIso :=
  functorIsoOfSimplicialHomotopy (coherentCospanConeValuePathHomotopy F X Y Z C)

end SerrePositivity.InfinityCategories.F2
