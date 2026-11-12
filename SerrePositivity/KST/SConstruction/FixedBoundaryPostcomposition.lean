module
public import SerrePositivity.KST.SConstruction.FixedBoundaryCospanComparison

/-! # 全境界固定の元の比較を実写像で後合成する
概要：元の比較円柱・高次比較・全境界固定の式を、同じ標的写像で後合成する。
方針：同じ全写像を後合成し、結合則と全三面の自然性を使う。
規約：新たな辺・円柱・高次比較を選ばず、元の全像を保持する。
使われ方：元の BF 回収比較を固定因子との豊穣合成へ写す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全比較時刻での元の境界固定は、同じ標的写像で後合成しても保持する。 -/
lemma fixedBoundaryHomotopy_postcomp {A T E B : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    {f g : T ⟶ E} (H : SSet.Homotopy f g)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) (p : E ⟶ B) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p).h = fst A Δ[1] ≫ b ≫ p := by
  change _ ≫ H.h ≫ p = _
  rw [← Category.assoc, hr, Category.assoc]

/-- 全高次比較の境界固定も、同じ写像での後合成で全体として保持する。 -/
lemma fixedBoundaryFamily_postcomp {A T U E B : SSet.{u}} (j : A ⟶ T) (b : A ⟶ E)
    (q : T ⊗ U ⟶ E) (hr : (j ▷ U) ≫ q = fst A U ≫ b) (p : E ⟶ B) :
    (j ▷ U) ≫ q ≫ p = fst A U ≫ b ≫ p := by
  rw [← Category.assoc, hr, Category.assoc]

end SerrePositivity.KST.SConstruction
