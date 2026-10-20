module
public import SerrePositivity.KST.SConstruction.FixedBoundaryHomotopyComposition

/-! # 元の始点境界を全時刻固定する比較の連結
概要：二つの元の相対円柱の始点境界から、同じ境界を固定する実合成を構成する。
方針：各全固定式を両端で評価して境界の等号を回収し、固定境界空間で合成する。
規約：二つの元の全円柱と実三角形を保持し、境界の一致を追加仮定にしない。
使われ方：累積補正の構造射像と次段の元の適合比較の連結。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全相対円柱の固定条件は、両端の同じ境界を厳密に回収する。 -/
lemma fixedBoundaryHomotopy_restrictions {A T E : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    j ≫ f = b ∧ j ≫ g = b := by
  constructor
  · have he := congrArg (SSet.ι₀ ≫ ·) hr
    simpa only [SSet.ι₀_comp_assoc, H.h₀, SSet.ι₀_fst_assoc] using he
  · have he := congrArg (SSet.ι₁ ≫ ·) hr
    simpa only [SSet.ι₁_comp_assoc, H.h₁, SSet.ι₁_fst_assoc] using he

/-- 元の各始点境界の固定式だけから、全境界を固定する実合成を内部構成する。 -/
def sourceFixedBoundaryComposition {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] {f g h : T ⟶ E}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy g h)
    (hH : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f)
    (hK : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = fst A Δ[1] ≫ j ≫ g) :
    FixedBoundaryCompositionData j (j ≫ f) H K := by
  have hg : j ≫ g = j ≫ f := (fixedBoundaryHomotopy_restrictions j (j ≫ f) H hH).2
  have hk : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = fst A Δ[1] ≫ (j ≫ f) := by
    rw [hK, hg]
  have hh : j ≫ h = j ≫ f := (fixedBoundaryHomotopy_restrictions j (j ≫ f) K hk).2
  exact fixedBoundaryCompositionData j (j ≫ f) rfl hg hh H K hH hk

end SerrePositivity.KST.SConstruction
