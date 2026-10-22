module
public import SerrePositivity.KST.SConstruction.DGModuleSquareHomotopyPostcompose
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaHomotopyIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePushout
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareVertices

/-! # 元の二軸 Yoneda 射の実 cofiber 四角形
概要：同じ右軸・元の対象・左軸代表と元の二射を持つ実押し出しを構成する。
方針：標準円錐四角形を元の円錐比較で後合成し、同じ比較のホモトピー可逆性を使う。
規約：四角形の二つの実二単体を保持。使われ方：実 dg 二軸分解の ∞ 余極限性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M

/-- 元の円錐比較で標準 cofiber データの終点だけを移した実四角形データ。 -/
def dgGluingAxesYonedaCofiberData :=
  (dgModuleConeSquareData R G (dgGluingAxesYonedaRightMap R C D M zc hc X)).postcompose
    (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X)

/-- 同じ四角形の右射は、元の左軸射影の Yoneda 像そのもの。 -/
lemma dgGluingAxesYonedaCofiberData_right :
    (dgGluingAxesYonedaCofiberData R C D M zc hc zd hd X).right =
      dgGluingAxesYonedaLeftMap R C D M zd hd X :=
  dgGluingAxesYonedaConeComparison_inr R C D M zc hc zd hd X

/-- 元の二軸代表と二射を持つ、全加群 nerve の実 cofiber 四角形。 -/
def dgGluingAxesYonedaCofiberSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) (max v w)}) ⟶ dgModuleNerve R G :=
  (dgGluingAxesYonedaCofiberData R C D M zc hc zd hd X).square

/-- 同じ実二軸四角形は、全加群 nerve で実際の ∞ 押し出し。 -/
lemma dgGluingAxesYonedaCofiberSquare_isPushout :
    IsPushoutSquare (dgGluingAxesYonedaCofiberSquare R C D M zc hc zd hd X) := by
  apply dgModuleSquare_isPushout_postcompose_homotopy _ _
    (dgGluingAxesYonedaConeComparison_isIso_homotopy R C D M zc hc zd hd X)
  rw [dgModuleConeSquareData_square]
  exact dgModuleConeSquare_isPushout R G _

/-- 同じ実押し出しの零角は、元の標準零加群を保持する。 -/
lemma dgGluingAxesYonedaCofiberSquare_zero :
    IsZeroVertex (squareVertex (dgGluingAxesYonedaCofiberSquare R C D M zc hc zd hd X) 0 1) := by
  change IsZeroVertex (squareVertex
    (dgGluingAxesYonedaCofiberData R C D M zc hc zd hd X).square 0 1)
  rw [DGModuleSquareData.square_vertex01]
  exact dgModuleNerveZeroVertex_isZero R G

/-- 同じ四角形の下辺は、元の右軸包含の Yoneda 像の実辺。 -/
lemma dgGluingAxesYonedaCofiberSquare_bottom :
    squareBottomEdge ≫ dgGluingAxesYonedaCofiberSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (dgModuleEdge R G
        (dgGluingAxesYonedaRightMap R C D M zc hc X)).edge :=
  DGModuleSquareData.square_bottom _

/-- 同じ四角形の右辺は、元の左軸射影の Yoneda 像の実辺。 -/
lemma dgGluingAxesYonedaCofiberSquare_right :
    squareRightEdge ≫ dgGluingAxesYonedaCofiberSquare R C D M zc hc zd hd X =
      SSet.yonedaEquiv.symm (dgModuleEdge R G
        (dgGluingAxesYonedaLeftMap R C D M zd hd X)).edge := by
  change squareRightEdge ≫ (dgGluingAxesYonedaCofiberData R C D M zc hc zd hd X).square = _
  rw [DGModuleSquareData.square_right, dgGluingAxesYonedaCofiberData_right]

end SerrePositivity.KST.SConstruction
