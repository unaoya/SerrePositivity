module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxComonoid

/-! # Serre 鎖立方体の全座標の面・退化・connection
概要：全有限 tensor 冪の各座標で、元の端点挿入・増大・max の射を作る。
方針：右端座標から数え、余モノイドの tensor と構造同型を使って帰納する。
規約：座標零は右端。基礎の射は元の鎖写像。使われ方：cubical rigidification の座標作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の端点を選ぶ Serre 余モノイド射。 -/
def serreIntervalEndpointComonHom (b : Bool) :
    𝟙_ (Comon (Complex A)) ⟶ serreIntervalComonoid A :=
  if b then serreIntervalOneComonHom A else serreIntervalZeroComonHom A

/-- 指定座標への元の端点の挿入。座標は右端から数える。 -/
def serreCubeFace (b : Bool) : (n : ℕ) → Fin (n + 1) →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A (n + 1))
  | 0, _ => (ρ_ (serreCubeComonoid A 0)).inv ≫
      (𝟙 (serreCubeComonoid A 0) ⊗ₘ serreIntervalEndpointComonHom A b)
  | n + 1, i => Fin.cases
      ((ρ_ (serreCubeComonoid A (n + 1))).inv ≫
        (𝟙 (serreCubeComonoid A (n + 1)) ⊗ₘ serreIntervalEndpointComonHom A b))
      (fun j => serreCubeFace b n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) i

/-- 指定座標の元の増大による削除。座標は右端から数える。 -/
def serreCubeDegeneracy : (n : ℕ) → Fin (n + 1) →
    (serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A n)
  | 0, _ => (𝟙 (serreCubeComonoid A 0) ⊗ₘ serreIntervalAugmentationComonHom A) ≫
      (ρ_ (serreCubeComonoid A 0)).hom
  | n + 1, i => Fin.cases
      ((𝟙 (serreCubeComonoid A (n + 1)) ⊗ₘ serreIntervalAugmentationComonHom A) ≫
        (ρ_ (serreCubeComonoid A (n + 1))).hom)
      (fun j => serreCubeDegeneracy n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) i

/-- 指定した隣接二座標を元の max で結合する connection。 -/
def serreCubeConnection : (n : ℕ) → Fin (n + 1) →
    (serreCubeComonoid A (n + 2) ⟶ serreCubeComonoid A (n + 1))
  | 0, _ => (α_ (serreCubeComonoid A 0)
      (serreIntervalComonoid A) (serreIntervalComonoid A)).hom ≫
        (𝟙 (serreCubeComonoid A 0) ⊗ₘ serreIntervalMaxComonHom A)
  | n + 1, i => Fin.cases
      ((α_ (serreCubeComonoid A (n + 1))
        (serreIntervalComonoid A) (serreIntervalComonoid A)).hom ≫
          (𝟙 (serreCubeComonoid A (n + 1)) ⊗ₘ serreIntervalMaxComonHom A))
      (fun j => serreCubeConnection n j ⊗ₘ 𝟙 (serreIntervalComonoid A)) i

end SerrePositivity.KST.SConstruction
