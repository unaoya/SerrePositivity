module
public import SerrePositivity.KST.SConstruction.FixedBoundaryCospanComparison
public import SerrePositivity.KST.SConstruction.SourceFixedBoundaryComposition

/-! # 同じ終点への元の二円柱から全境界固定比較を回収
概要：元の各始点境界を固定する二円柱が同じ終点を持てば、共通終点境界で実比較する。
方針：元の固定式の終端制限から境界の厳密な一致を証明し、同じ実 cospan を貼る。
規約：境界の一致を追加仮定にせず、元の全二円柱を同じ高次比較の面に保持する。
使われ方：左右結合の直接補正を同じ単一射補正を通して実比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の二脚の全境界固定式から、同じ終点境界を固定する全比較と実三角形を構成する。 -/
def targetFixedBoundaryCospan {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] {f g h : T ⟶ E} (H : Homotopy f h) (K : Homotopy g h)
    (hH : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f)
    (hK : (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = fst A Δ[1] ≫ j ≫ g) :
    FixedBoundaryCospanData j (j ≫ h) H K := by
  have hf : j ≫ f = j ≫ h := (fixedBoundaryHomotopy_restrictions j (j ≫ f) H hH).2.symm
  have hg : j ≫ g = j ≫ h := (fixedBoundaryHomotopy_restrictions j (j ≫ g) K hK).2.symm
  exact fixedBoundaryCospanData j (j ≫ h) hf hg rfl H K
    (hH.trans (congrArg (fst A Δ[1] ≫ ·) hf))
    (hK.trans (congrArg (fst A Δ[1] ≫ ·) hg))

end SerrePositivity.KST.SConstruction
