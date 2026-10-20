module

public import SerrePositivity.InfinityCategories.F2.CoconeVariablePrism
public import SerrePositivity.InfinityCategories.F2.PointHomTransportCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomFamily

/-!
概要：元の native な余錐の全 Hom の輸送から変換の正方形を構成する。
方針：元の輸送円柱を、可変頂点の余錐の円柱で評価する。
規約：元の余錐と全 Hom の族を選び直さない。
使われ方：指定三角形による全空間比較の合成整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X}

/-- 概要：指定余錐の全 Hom の輸送による二方向の円柱を評価する。
方針：N の実際の輸送を余錐の全円柱へ入力する。
規約：横が元の図式から頂点、縦が全 Hom の輸送。使われ方：合成三角形の正方形表示。 -/
def coconePointHomSquare (c : JoinCocone f) (z : X _⦋0⦌) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})) ⟶ X :=
  coconeVariablePrism (pointHomTransportCylinder (sliceUnderProjection f) c z).h

/-- 概要：正方形の横の始点は全時刻で元の図式。
方針：可変頂点の余錐の始点の式を使う。
規約：全 Hom のパラメータを保持。使われ方：三角形の固定辺。 -/
lemma coconePointHomSquare_zero (c : JoinCocone f) (z : X _⦋0⦌) :
    (SSet.ι₀ ▷ (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u}))) ≫
      coconePointHomSquare c z = fst K (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})) ≫ f :=
  coconeVariablePrism_zero _

/-- 概要：正方形の横の終点は元の全 Hom の輸送円柱の頂点射影。
方針：可変頂点の円柱の終点を計算する。
規約：全時間での等式。使われ方：三角形の底の辺の追跡。 -/
lemma coconePointHomSquare_one (c : JoinCocone f) (z : X _⦋0⦌) :
    (SSet.ι₁ ▷ (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u}))) ≫
      coconePointHomSquare c z = snd K (pinchedHomLeft c.vertex z ⊗ (Δ[1] : SSet.{u})) ≫
        (pointHomTransportCylinder (sliceUnderProjection f) c z).h ≫ sliceUnderProjection f :=
  coconeVariablePrism_one _

/-- 概要：縦の始点の変換は元の指定余錐の定値族。
方針：パラメータ自然性と輸送円柱の始点を使う。
規約：余錐を選び直さない。使われ方：合成の第一辺の同定。 -/
lemma coconePointHomSquare_source (c : JoinCocone f) (z : X _⦋0⦌) :
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀) ≫ coconePointHomSquare c z =
      coconeVariablePrism (SSet.const c : pinchedHomLeft c.vertex z ⟶ sliceUnder f) := by
  rw [coconePointHomSquare, ← coconeVariablePrism_precomp]
  congr 1
  exact (pointHomTransportCylinder (sliceUnderProjection f) c z).h₀

/-- 概要：縦の終点は元の全 Hom の余錐の族の標準変換の円柱そのもの。
方針：パラメータ自然性と輸送の終点の厳密な式を使う。
規約：同値類へ落とさない。使われ方：合成の長辺と元の比較射の接続。 -/
lemma coconePointHomSquare_target (c : JoinCocone f) (z : X _⦋0⦌) :
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₁) ≫ coconePointHomSquare c z =
      coconeParameterPrism (coconePointHomFamily c z) := by
  rw [coconePointHomSquare, ← coconeVariablePrism_precomp]
  change coconeVariablePrism _ = coconeVariablePrism _
  congr 1
  exact (pointHomTransportCylinder (sliceUnderProjection f) c z).h₁

end SerrePositivity.InfinityCategories.F2
