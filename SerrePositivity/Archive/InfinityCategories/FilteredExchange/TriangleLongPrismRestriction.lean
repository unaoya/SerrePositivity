module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：始点固定の全三角形の延長空間を、同じ長辺の prism 延長空間へ制限する。
方針：最初の頂点と長辺の可換正方形に相対延長の制限を適用する。
規約：元の全円柱と指定同型を保持。使われ方：全錐の比較と元の局所長辺比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 長辺 prism の始点は、全三角形の同じ最初の頂点である。 -/
lemma triangleLongPrism_initial_square (A : SSet.{u}) :
    prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      simplexPrismVertex 0 0 A ≫ (scaffoldFirstVertex 2 ▷ A) := by
  apply SSet.hom_ext
  intro n
  rfl

open CartesianMonoidalCategory
variable {A E B : SSet.{u}} (p : E ⟶ B) (b : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
  (v : (Δ[0] : SSet.{u}) ⊗ A ⟶ E) (hv : v ≫ p = (scaffoldFirstVertex 2 ▷ A) ≫ b)
local notation "j" => stdSimplex.δ (1 : Fin 3) ▷ A
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "s" => simplexPrismVertex 0 0 A ≫ v
include hv in
/-- 長辺へ制限しても元の始点を被覆する条件を保持する。 -/
lemma triangleLongPrism_initial : s ≫ p = prismEndpoint 0 A ≫ (j ≫ b) := by
  rw [Category.assoc, hv, ← Category.assoc, ← triangleLongPrism_initial_square, Category.assoc]

local notation "hvs" => triangleLongPrism_initial p b v hv

/-- 元の全三角形を、同じ始点と底の長辺を持つ全 prism に制限する射。 -/
def triangleLongPrismExtensionRestriction :
    relativeFunctorExtensionSpace p b i v hv ⟶
      relativeFunctorExtensionSpace p (j ≫ b) (prismEndpoint 0 A) s hvs :=
  relativeExtensionRestriction p b i v hv j (simplexPrismVertex 0 0 A) (prismEndpoint 0 A)
    (triangleLongPrism_initial_square A)

/-- 制限先は長辺の始点を固定した可縮な prism 延長空間。 -/
lemma triangleLongPrismExtension_contractible [LeftFibration p] :
    IsContractibleKan
      (relativeFunctorExtensionSpace p (j ≫ b) (prismEndpoint 0 A) s hvs) :=
  relativeFunctorExtensionSpace_isContractibleKan p (j ≫ b) (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) s hvs

/-- 元の全三角形の実際の制限頂点は、その同じ長辺の全円柱を表す。 -/
lemma triangleLongPrismExtensionRestriction_vertex_value
    (W : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v) :
    (((triangleLongPrismExtensionRestriction p b v hv).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩)).val).val =
        functorVertex (j ≫ W) := by
  exact congrArg (fun z => z.val.val)
    (relativeExtensionRestriction_vertex p b i v hv j (simplexPrismVertex 0 0 A) (prismEndpoint 0 A)
      (triangleLongPrism_initial_square A) W hW hWi)

/-- 指定三角形比較の長辺への像は、同じ二円柱間の標準の指定比較に等しい。 -/
lemma triangleLongPrismExtensionRestriction_vertexIso [LeftFibration p]
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (triangleLongPrismExtensionRestriction p b v hv) =
      (triangleLongPrismExtension_contractible p b v hv).vertexIso
        ((triangleLongPrismExtensionRestriction p b v hv).app (Opposite.op ⦋0⦌) x)
        ((triangleLongPrismExtensionRestriction p b v hv).app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible (triangleLongPrismExtension_contractible p b v hv) e _

end SerrePositivity.InfinityCategories.F2
