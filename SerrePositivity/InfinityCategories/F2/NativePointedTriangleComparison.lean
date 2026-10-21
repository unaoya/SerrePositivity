module

public import SerrePositivity.InfinityCategories.F2.NativePointedConeTriangleLift
public import SerrePositivity.InfinityCategories.F2.ContractibleVertexIsoNaturality

/-!
概要：全錐から制限した三角形と既存の持ち上げを、始点固定の同じ選択空間で比較する。
方針：最初の頂点包含の left anodyne 性から可縮な延長空間の指定同型を取る。
規約：底・全二単体・始点族を固定。使われ方：元の二三角形を共通の全錐と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌)
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ s
local notation "b" => fst Δ[2] A ≫ D
local notation "hv" => nativePointedConeTriangle_initial c s hs k

/-- 元の native 三角形の底と同じ全始点族を固定した選択空間。 -/
def nativePointedTriangleExtensionSpace : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection b i v hv

/-- 全三角形の始点固定の選択空間は可縮であり、底の形状の仮定は不要。 -/
lemma nativePointedTriangleExtensionSpace_contractible :
    IsContractibleKan (nativePointedTriangleExtensionSpace c s hs k) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne 2) A) v hv

/-- 底と始点を保つ実際の全三角形を同じ選択空間の頂点として表示する。 -/
def nativePointedTriangleExtensionVertex (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = b) (hH₀ : i ≫ H = v) :
    (nativePointedTriangleExtensionSpace c s hs k) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection b i v hv ⟨H, hH, hH₀⟩

/-- 全錐からの制限と既存の全三角形の指定比較。全高次の始点条件も型に保持する。 -/
def nativePointedTriangleComparisonIso
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = b) (hH₀ : i ≫ H = v) :
    VertexIso
      (nativePointedTriangleExtensionVertex c s hs k (nativePointedConeTriangleLift c s hs k)
        (nativePointedConeTriangleLift_projection c s hs k)
        (nativePointedConeTriangleLift_initial c s hs k))
      (nativePointedTriangleExtensionVertex c s hs k H hH hH₀) :=
  (nativePointedTriangleExtensionSpace_contractible c s hs k).vertexIso _ _

end SerrePositivity.InfinityCategories.F2
