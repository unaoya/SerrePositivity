module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilies
public import SerrePositivity.InfinityCategories.F1.PointCoslicePostIso

/-!
概要：実際の辺による coslice の前合成を、両始点の表示を揃えて固定終点の fiber に制限する。
方針：終点側の等号移送・合成三角形の切断・始点側の等号移送を合成する。
規約：辺の両端を点図式の等号で指定し、可変終点の全単体を厳密に保つ。
使われ方：部分余極限の Hom 図式の射を実際の写像空間の射として構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (a b : (Δ[0] : SSet.{u}) ⟶ X)
  (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)

/-- 両側の始点の表示を正規化した、実際の辺による coslice の前合成。 -/
def cosliceEdgePrecompositionAt : sliceUnder b ⟶ sliceUnder a :=
  eqToHom (congrArg sliceUnder hb.symm) ≫ cosliceEdgePrecomposition e ≫
    eqToHom (congrArg sliceUnder ha)

/-- 始点の表示を正規化しても、可変終点の射影は厳密に保たれる。 -/
lemma cosliceEdgePrecompositionAt_projection :
    cosliceEdgePrecompositionAt e a b ha hb ≫ sliceUnderProjection a = sliceUnderProjection b := by
  simp only [cosliceEdgePrecompositionAt, Category.assoc]
  erw [sliceUnder_eqToHom_projection ha]
  rw [cosliceEdgePrecomposition_projection]
  exact sliceUnder_eqToHom_projection hb.symm

/-- 実際の辺の前合成を、同じ可変終点 y を固定した二つの写像空間の射へ制限する。 -/
def cosliceEdgeFiberPrecomposition (y : X _⦋0⦌) :
    vertexFiber (sliceUnderProjection b) y ⟶ vertexFiber (sliceUnderProjection a) y :=
  vertexFiberMap _ _ (cosliceEdgePrecompositionAt e a b ha hb)
    (cosliceEdgePrecompositionAt_projection e a b ha hb) y

/-- 固定終点の前合成を含め直すと、coslice 全体の前合成になる。 -/
lemma cosliceEdgeFiberPrecomposition_ι (y : X _⦋0⦌) :
    cosliceEdgeFiberPrecomposition e a b ha hb y ≫ vertexFiberι (sliceUnderProjection a) y =
      vertexFiberι (sliceUnderProjection b) y ≫ cosliceEdgePrecompositionAt e a b ha hb :=
  vertexFiberMap_ι _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
