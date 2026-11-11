module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpanPointHomCospan

/-!
概要：実際の二辺を使う点 Hom の cospan を、三つの点図式の表示変更で厳密に移す。
方針：固定終点の fiber の等号同型を成分とし、前合成の自然性を等号消去で証明する。
規約：辺の選択は保持する。使われ方：ホーン表示と部分余極限の左 Hom の cospan の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 点図式の等号による固定終点の余錐空間の厳密な同型。 -/
def pointCoconeMappingIso {a b : (Δ[0] : SSet.{u}) ⟶ X} (h : a = b) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace b y :=
  eqToIso (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace t y) h)

/-- 指定した二辺による、固定終点の点 Hom の cospan。 -/
def pointHomCospan (a b c : (Δ[0] : SSet.{u}) ⟶ X)
    (eB eC : (Δ[1] : SSet.{u}) ⟶ X)
    (hBs : stdSimplex.δ (1 : Fin 2) ≫ eB = a)
    (hBt : stdSimplex.δ (0 : Fin 2) ≫ eB = b)
    (hCs : stdSimplex.δ (1 : Fin 2) ≫ eC = a)
    (hCt : stdSimplex.δ (0 : Fin 2) ≫ eC = c) (y : X _⦋0⦌) :
    AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition eC a c hCs hCt y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition eB a b hBs hBt y)

/-- 前合成は両端の点図式の表示変更と厳密に可換。 -/
lemma cosliceEdgeFiberPrecomposition_points {a b a' b' : (Δ[0] : SSet.{u}) ⟶ X}
    (e : (Δ[1] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)
    (ha' : stdSimplex.δ (1 : Fin 2) ≫ e = a')
    (hb' : stdSimplex.δ (0 : Fin 2) ≫ e = b')
    (hA : a = a') (hB : b = b') (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition e a b ha hb y ≫ (pointCoconeMappingIso hA y).hom =
      (pointCoconeMappingIso hB y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition e a' b' ha' hb' y := by
  cases hA
  cases hB
  simp only [pointCoconeMappingIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  erw [Category.comp_id]

/-- 同じ二辺の点 Hom の cospan は、三点の表示変更で自然同型。 -/
def pointHomCospanPointsIso {a b c a' b' c' : (Δ[0] : SSet.{u}) ⟶ X}
    (eB eC : (Δ[1] : SSet.{u}) ⟶ X)
    (hBs : stdSimplex.δ (1 : Fin 2) ≫ eB = a)
    (hBt : stdSimplex.δ (0 : Fin 2) ≫ eB = b)
    (hCs : stdSimplex.δ (1 : Fin 2) ≫ eC = a)
    (hCt : stdSimplex.δ (0 : Fin 2) ≫ eC = c)
    (hBs' : stdSimplex.δ (1 : Fin 2) ≫ eB = a')
    (hBt' : stdSimplex.δ (0 : Fin 2) ≫ eB = b')
    (hCs' : stdSimplex.δ (1 : Fin 2) ≫ eC = a')
    (hCt' : stdSimplex.δ (0 : Fin 2) ≫ eC = c')
    (hA : a = a') (hB : b = b') (hC : c = c') (y : X _⦋0⦌) :
    pointHomCospan a b c eB eC hBs hBt hCs hCt y ≅
      pointHomCospan a' b' c' eB eC hBs' hBt' hCs' hCt' y :=
  Functor.isoWhiskerLeft AsSmall.down (cospanIsoMk
    (pointCoconeMappingIso hA y) (pointCoconeMappingIso hC y) (pointCoconeMappingIso hB y)
    (cosliceEdgeFiberPrecomposition_points eC hCs hCt hCs' hCt' hA hC y)
    (cosliceEdgeFiberPrecomposition_points eB hBs hBt hBs' hBt' hA hB y))

/-- 二辺と三点の表示が一致すれば、二つの点 Hom の cospan は厳密に自然同型。 -/
def pointHomCospanPresentationIso {a b c a' b' c' : (Δ[0] : SSet.{u}) ⟶ X}
    {eB eC eB' eC' : (Δ[1] : SSet.{u}) ⟶ X}
    (hBs : stdSimplex.δ (1 : Fin 2) ≫ eB = a)
    (hBt : stdSimplex.δ (0 : Fin 2) ≫ eB = b)
    (hCs : stdSimplex.δ (1 : Fin 2) ≫ eC = a)
    (hCt : stdSimplex.δ (0 : Fin 2) ≫ eC = c)
    (hBs' : stdSimplex.δ (1 : Fin 2) ≫ eB' = a')
    (hBt' : stdSimplex.δ (0 : Fin 2) ≫ eB' = b')
    (hCs' : stdSimplex.δ (1 : Fin 2) ≫ eC' = a')
    (hCt' : stdSimplex.δ (0 : Fin 2) ≫ eC' = c')
    (hEB : eB = eB') (hEC : eC = eC')
    (hA : a = a') (hB : b = b') (hC : c = c') (y : X _⦋0⦌) :
    pointHomCospan a b c eB eC hBs hBt hCs hCt y ≅
      pointHomCospan a' b' c' eB' eC' hBs' hBt' hCs' hCt' y := by
  cases hEB
  cases hEC
  exact pointHomCospanPointsIso eB eC hBs hBt hCs hCt hBs' hBt' hCs' hCt' hA hB hC y

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
