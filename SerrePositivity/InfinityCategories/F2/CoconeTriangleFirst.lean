module

public import SerrePositivity.InfinityCategories.F2.CoconePointHomTriangle
public import SerrePositivity.InfinityCategories.F2.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationFamilyDiagram

/-!
概要：元の全 Hom の三角形の第一辺を、元の指定余錐の標準変換の族と同定する。
方針：円柱の全パラメータ比較を定値族へ適用する。
規約：余錐も変換も選び直さない。
使われ方：指定三角形上の unstraightening の比較の第一変換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X T : SSet.{u}} {f : K ⟶ X}

/-- 概要：元の余錐の定値変換の円柱は元の余錐の定値族の円柱。
方針：標準比較の全パラメータの式と定値射の後合成の式を使う。
規約：元の余錐そのもの。使われ方：三角形の第一辺の同定。 -/
lemma coconeTransformationVertex_const_prism (c : JoinCocone f) :
    constantTransformationPrism (SSet.const (coconeTransformationVertex c) : T ⟶ _) =
      coconeVariablePrism (SSet.const c : T ⟶ sliceUnder f) := by
  rw [show (SSet.const (coconeTransformationVertex c) : T ⟶ _) =
    SSet.const (coconeMappingPoint c) ≫ coconeTransformationMap f c.vertex from
      (SSet.const_comp _ _).symm, coconeTransformationMap_prism]
  change joinCylinderMap K T ≫ sliceUnderUncurry
    ((SSet.const (coconeMappingPoint c)) ≫ vertexFiberι (sliceUnderProjection f) c.vertex) = _
  rw [SSet.const_comp]
  rfl

/-- 概要：元の全 Hom の三角形の第一辺は元の余錐の標準変換の定値族。
方針：元の第一辺の円柱と coherent な変換の評価の座標を照合する。
規約：全 Hom のパラメータを保つ。使われ方：合成則の第一辺の正規化。 -/
lemma coconePointHomTriangle_first_transformation
    {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ pinchedHomLeft c.vertex z)) ≫
      coconePointHomTriangle c z = coherentTransformationFamilyDiagram
        (SSet.const (coconeTransformationVertex c) : pinchedHomLeft c.vertex z ⟶ _) := by
  rw [coconePointHomTriangle_first, ← coconeTransformationVertex_const_prism]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.F2
