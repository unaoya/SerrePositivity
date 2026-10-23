module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeDiagonalPrismHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTransformationHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.F1.Coherent.TransformationFamilyDiagram

/-!
概要：元の三角形の対角を変換空間へ戻し、元の余錐の全 Hom の標準変換と比較する。
方針：両端固定の円柱の最大値変形を全パラメータで curry する。
規約：元の図式・指定頂点・全 Hom の族を保持する。
使われ方：指定三角形による全空間比較の長辺を実際の余錐比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 概要：元の正方形の対角を同じ両端の変換の族へ戻す。
方針：元の対角の円柱を二端固定で curry する。
規約：元の対角そのもの。使われ方：指定三角形の長辺の変換。 -/
def coconeDiagonalTransformation (c : JoinCocone f) (z : X _⦋0⦌) :
    pinchedHomLeft c.vertex z ⟶
      intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z)) :=
  constantTransformationCurry (coconeDiagonalPrism c z)
    (coconeDiagonalPrism_zero c z) (coconeDiagonalPrism_one c z)

/-- 概要：対角の変換を円柱に戻すと元の対角。
方針：二端固定 curry の往復。規約：厳密な一致。使われ方：三角形との照合。 -/
lemma coconeDiagonalTransformation_prism (c : JoinCocone f) (z : X _⦋0⦌) :
    constantTransformationPrism (coconeDiagonalTransformation c z) = coconeDiagonalPrism c z :=
  constantTransformationPrism_curry _ _ _

/-- 概要：対角の変換と元の全 Hom の余錐族の標準変換を実際のホモトピーで結ぶ。
方針：最大値変形の全円柱を固定した二端とともに変換空間へ戻す。
規約：全 Hom の全高次パラメータ。使われ方：合成則の長辺の比較。 -/
def coconeDiagonalTransformationHomotopy (c : JoinCocone f) (z : X _⦋0⦌) :
    SSet.Homotopy (coconeDiagonalTransformation c z)
      (coconePointHomFamily c z ≫ coconeTransformationMap f z) := by
  let H := coconeDiagonalPrismHomotopy c z
  have ha := coconeDiagonalTransformation_prism c z
  have hb := coconeTransformationMap_prism (coconePointHomFamily c z)
  let H' : SSet.Homotopy (constantTransformationPrism (coconeDiagonalTransformation c z))
      (constantTransformationPrism (coconePointHomFamily c z ≫ coconeTransformationMap f z)) :=
    ⟨H.h, H.h₀.trans ha.symm, H.h₁.trans hb.symm, H.rel⟩
  exact constantTransformationHomotopyOfPrisms _ _ H'
    (coconeDiagonalPrismHomotopy_left c z) (coconeDiagonalPrismHomotopy_right c z)

/-- 概要：空間値の元の全 Hom 三角形の長辺は対角の変換の族そのもの。
方針：元の三角形の対角の円柱を coherent な族の座標へ移す。
規約：全パラメータで厳密な一致。使われ方：unstraightening の合成則の長辺。 -/
lemma coconePointHomTriangle_diagonal_transformation
    {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z =
        coherentTransformationFamilyDiagram (coconeDiagonalTransformation c z) := by
  rw [coconeDiagonalPrism_triangle, ← coconeDiagonalTransformation_prism]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
