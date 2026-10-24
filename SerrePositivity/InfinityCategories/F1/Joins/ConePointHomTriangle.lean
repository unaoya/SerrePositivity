module

public import SerrePositivity.InfinityCategories.F1.Joins.ConePointHomSquare
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeSquareParameters

/-!
概要：元の錐の right Hom 正方形の三角形と、その三辺の厳密な式を構成する。
方針：第一の標準三角形を取り、元の Hom の辺と指定錐の辺を照合する。
規約：元の全 Hom・元の指定錐・長辺の対角を選び直さない。
使われ方：定値始域の二変換の unstraightening の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 元の正方形の第一標準三角形。 -/
def conePointHomTriangle (c : JoinCone f) (x : X _⦋0⦌) :
    (Δ[2] : SSet.{u}) ⊗ (K ⊗ pinchedHom x c.vertex) ⟶ X :=
  (squareTriangle 0 ▷ (K ⊗ pinchedHom x c.vertex)) ≫
    F2.coconeSquareParameters K (pinchedHom x c.vertex) ≫ conePointHomSquare c x

/-- 三角形の第一辺は元の全 Hom の標準区間比較を定値図式へ移したもの。 -/
lemma conePointHomTriangle_first (c : JoinCone f) (x : X _⦋0⦌) :
    (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ pinchedHom x c.vertex)) ≫ conePointHomTriangle c x =
      F2.coconeVerticalParameters K (pinchedHom x c.vertex) ≫
        snd K (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})) ≫
          (β_ (pinchedHom x c.vertex) (Δ[1] : SSet.{u})).hom ≫
            intervalMappingUncurry (pinchedHomToIntervalMappingSpace x c.vertex) := by
  rw [conePointHomTriangle, ← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
    SerrePositivity.InfinityCategories.squareTriangle_outerFaces.1]
  change (F2.coconeVerticalParameters K (pinchedHom x c.vertex) ≫
    (SSet.ι₀ ▷ (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})))) ≫ conePointHomSquare c x = _
  rw [Category.assoc, conePointHomSquare_zero_standard]

/-- 三角形の第二辺は、同じ指定錐の定値族の円柱。 -/
lemma conePointHomTriangle_second (c : JoinCone f) (x : X _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ pinchedHom x c.vertex)) ≫ conePointHomTriangle c x =
      F2.coconeHorizontalParameters K (pinchedHom x c.vertex) ≫
        coneVariablePrism (SSet.const c : pinchedHom x c.vertex ⟶ sliceOver f) := by
  rw [conePointHomTriangle, ← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
    SerrePositivity.InfinityCategories.squareTriangle_outerFaces.2.1]
  change (F2.coconeHorizontalParameters K (pinchedHom x c.vertex) ≫
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₁)) ≫ conePointHomSquare c x = _
  rw [Category.assoc, conePointHomSquare_target]

/-- 元の三角形の長辺は、元の正方形の同じ対角。 -/
lemma conePointHomTriangle_diagonal (c : JoinCone f) (x : X _⦋0⦌) :
    (stdSimplex.δ (1 : Fin 3) ▷ (K ⊗ pinchedHom x c.vertex)) ≫ conePointHomTriangle c x =
      (squareDiagonal ▷ (K ⊗ pinchedHom x c.vertex)) ≫
        F2.coconeSquareParameters K (pinchedHom x c.vertex) ≫ conePointHomSquare c x := by
  rw [conePointHomTriangle, ← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
    squareTriangle_diagonal, Category.assoc]

end SerrePositivity.InfinityCategories
