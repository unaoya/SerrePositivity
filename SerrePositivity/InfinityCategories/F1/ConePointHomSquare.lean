module

public import SerrePositivity.InfinityCategories.F1.ConeVariablePrism
public import SerrePositivity.InfinityCategories.F1.RightPointHomTransportBase
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedApexLimitCriterion

/-!
概要：元の native な錐の全 Hom 比較と right 輸送から、合成を表す正方形を作る。
方針：元の選択済み輸送円柱を可変頂点の錐の普遍族で評価する。
規約：四辺は元の比較・元の錐・同じ標準 Hom の辺を厳密に保持する。
使われ方：全試験空間の比較を定値始域の変換の相対合成へ移す。
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

/-- 元の全 Hom の right 輸送が定める、元の錐の二方向の円柱。 -/
def conePointHomSquare (c : JoinCone f) (x : X _⦋0⦌) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})) ⟶ X :=
  coneVariablePrism (rightPointHomTransportCylinder (sliceOverProjection f) c x).h

/-- 横の始点は元の Hom の輸送円柱の頂点射影。 -/
lemma conePointHomSquare_zero (c : JoinCone f) (x : X _⦋0⦌) :
    (SSet.ι₀ ▷ (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u}))) ≫ conePointHomSquare c x =
      snd K (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})) ≫
        (rightPointHomTransportCylinder (sliceOverProjection f) c x).h ≫ sliceOverProjection f :=
  coneVariablePrism_zero _

/-- 横の終点は全時刻で同じ元の図式に固定される。 -/
lemma conePointHomSquare_one (c : JoinCone f) (x : X _⦋0⦌) :
    (SSet.ι₁ ▷ (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u}))) ≫ conePointHomSquare c x =
      fst K (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})) ≫ f :=
  coneVariablePrism_one _

/-- 縦の始点は元の全 Hom の native な錐への同じ比較そのもの。 -/
lemma conePointHomSquare_source (c : JoinCone f) (x : X _⦋0⦌) :
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀) ≫ conePointHomSquare c x =
      coneParameterPrism (fixedApexConeHomComparison c x) := by
  rw [conePointHomSquare, ← coneVariablePrism_precomp]
  change coneVariablePrism _ = _
  rw [(rightPointHomTransportCylinder (sliceOverProjection f) c x).h₀,
    coneVariablePrism_fixed]
  rfl

/-- 縦の終点は同じ指定錐の定値族。 -/
lemma conePointHomSquare_target (c : JoinCone f) (x : X _⦋0⦌) :
    ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₁) ≫ conePointHomSquare c x =
      coneVariablePrism (SSet.const c : pinchedHom x c.vertex ⟶ sliceOver f) := by
  rw [conePointHomSquare, ← coneVariablePrism_precomp]
  change coneVariablePrism _ = _
  rw [(rightPointHomTransportCylinder (sliceOverProjection f) c x).h₁]

/-- 横の始点の底は元の全 Hom の標準区間比較の円柱そのもの。 -/
lemma conePointHomSquare_zero_standard (c : JoinCone f) (x : X _⦋0⦌) :
    (SSet.ι₀ ▷ (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u}))) ≫ conePointHomSquare c x =
      snd K (pinchedHom x c.vertex ⊗ (Δ[1] : SSet.{u})) ≫
        (β_ (pinchedHom x c.vertex) (Δ[1] : SSet.{u})).hom ≫
          intervalMappingUncurry (pinchedHomToIntervalMappingSpace x c.vertex) := by
  rw [conePointHomSquare_zero, rightPointHomTransportCylinder_base]
  rfl

end SerrePositivity.InfinityCategories
