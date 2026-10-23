module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeSquareParameters
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.PointHomTransportBase

/-!
概要：元の余錐の全 Hom の正方形の標準三角形とその三辺を構成する。
方針：正方形の第二の標準三角形へ制限し、各辺の元の族を照合する。
規約：三角形も全 Hom の族も実際の射として保持する。
使われ方：指定三角形に沿う unstraightening の合成則への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 概要：指定余錐と全 Hom の輸送が定める実際の三角形の族。
方針：元の正方形の第二三角形を図式・Hom の全パラメータで評価する。
規約：長辺は元の正方形の対角。使われ方：全 Hom の合成の比較。 -/
def coconePointHomTriangle (c : JoinCocone f) (z : X _⦋0⦌) :
    (Δ[2] : SSet.{u}) ⊗ (K ⊗ pinchedHomLeft c.vertex z) ⟶ X :=
  (squareTriangle 1 ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
    coconeSquareParameters K (pinchedHomLeft c.vertex z) ≫ coconePointHomSquare c z

/-- 概要：三角形の第一辺は元の指定余錐の定値族の円柱。
方針：正方形の下辺への制限と、輸送の始点の式を使う。
規約：全 Hom のパラメータを保持。使われ方：合成の第一変換の同定。 -/
lemma coconePointHomTriangle_first (c : JoinCocone f) (z : X _⦋0⦌) :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z = coconeHorizontalParameters K (pinchedHomLeft c.vertex z) ≫
        coconeVariablePrism (SSet.const c : pinchedHomLeft c.vertex z ⟶ sliceUnder f) := by
  have he : stdSimplex.δ (2 : Fin 3) ≫ squareTriangle.{u} 1 =
      (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) :=
    kanSquareTriangle_outerFaces.2.2.1
  rw [coconePointHomTriangle, ← Category.assoc, ← Category.assoc,
    ← comp_whiskerRight, he]
  change (coconeHorizontalParameters K (pinchedHomLeft c.vertex z) ≫
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀)) ≫ coconePointHomSquare c z = _
  rw [Category.assoc, coconePointHomSquare_source]

/-- 概要：三角形の第二辺は元の全 Hom の輸送円柱の底への射影。
方針：正方形の右辺の終点の式を使う。
規約：元の左 Hom の全時間の辺。使われ方：合成の第二変換の同定。 -/
lemma coconePointHomTriangle_second (c : JoinCocone f) (z : X _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z = coconeVerticalParameters K (pinchedHomLeft c.vertex z) ≫
        snd K (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})) ≫
          (pointHomTransportCylinder (sliceUnderProjection f) c z).h ≫ sliceUnderProjection f := by
  rw [coconePointHomTriangle, ← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
    kanSquareTriangle_outerFaces.2.2.2]
  change (coconeVerticalParameters K (pinchedHomLeft c.vertex z) ≫
    (SSet.ι₁ ▷ (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})))) ≫
      coconePointHomSquare c z = _
  rw [Category.assoc, coconePointHomSquare_one]

/-- 概要：第二辺は元の左 Hom の標準区間比較を図式上で定値にしたもの。
方針：元の輸送円柱の底の厳密な式を使う。
規約：元の Hom の辺。使われ方：定値標的への作用の追跡。 -/
lemma coconePointHomTriangle_second_standard (c : JoinCocone f) (z : X _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z = coconeVerticalParameters K (pinchedHomLeft c.vertex z) ≫
        snd K (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})) ≫
          (β_ (pinchedHomLeft c.vertex z) (Δ[1] : SSet.{u})).hom ≫
            intervalMappingUncurry (pinchedHomLeftToIntervalMappingSpace c.vertex z) := by
  rw [coconePointHomTriangle_second, pointHomTransportCylinder_base]
  rfl

/-- 概要：長辺は元の正方形の対角を全パラメータで制限したもの。
方針：標準二三角形の共通面の式を使う。
規約：対角を選び直さない。使われ方：元の余錐の族との対角の比較。 -/
lemma coconePointHomTriangle_diagonal (c : JoinCocone f) (z : X _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z = (squareDiagonal ▷ (K ⊗ pinchedHomLeft c.vertex z)) ≫
        coconeSquareParameters K (pinchedHomLeft c.vertex z) ≫ coconePointHomSquare c z := by
  rw [coconePointHomTriangle, ← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_diagonal, Category.assoc]

end SerrePositivity.InfinityCategories.F2
