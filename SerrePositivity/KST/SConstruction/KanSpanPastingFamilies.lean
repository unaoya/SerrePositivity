module
public import SerrePositivity.KST.SConstruction.KanSpanSpecifiedPasting

/-! # 二つの元の脚を全パラメータで保持する普遍三角形族
概要：全貼り合わせの選択を、元の二脚を固定する一つの実二単体族として評価する。
方針：延長選択空間の普遍評価を使い、ホーンの二つの面の制限を照合する。
規約：頂点での存在だけでなく、全高次選択と全ての元の二脚を同時に保持する。
使われ方：元の K square の二三角形の貼り合わせを全選択パラメータで追跡する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全ての貼り合わせ三角形を同時に評価する元の実族。 -/
def kanSpanPastingFamily {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    (Δ[2] : SSet.{u}) ⊗ kanSpanPastingChoices a b ⟶ K :=
  anodyneExtensionFamily _ (kanSpanHorn a b)

/-- 普遍族の第一脚は元の第一辺であり、全選択パラメータで変わらない。 -/
lemma kanSpanPastingFamily_source {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    (stdSimplex.δ 2 ▷ kanSpanPastingChoices a b) ≫ kanSpanPastingFamily a b =
      fst (Δ[1] : SSet.{u}) (kanSpanPastingChoices a b) ≫ SSet.yonedaEquiv.symm a.edge := by
  have hf := anodyneExtensionFamily_fac (horn 2 (0 : Fin 3)).ι (kanSpanHorn a b)
  change ((horn 2 (0 : Fin 3)).ι ▷ kanSpanPastingChoices a b) ≫
    kanSpanPastingFamily a b =
      fst (Λ[2, 0] : SSet.{u}) (kanSpanPastingChoices a b) ≫ kanSpanHorn a b at hf
  have he : (stdSimplex.δ 2 : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      horn₂₀.ι₀₁ ≫ (horn 2 (0 : Fin 3)).ι := (horn.ι_ι _ _ (by decide)).symm
  rw [he, comp_whiskerRight_assoc, hf, whiskerRight_fst_assoc, kanSpanHorn_source]

/-- 普遍族の第二脚も元の第二辺であり、全高次選択で厳密に保たれる。 -/
lemma kanSpanPastingFamily_target {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    (stdSimplex.δ 1 ▷ kanSpanPastingChoices a b) ≫ kanSpanPastingFamily a b =
      fst (Δ[1] : SSet.{u}) (kanSpanPastingChoices a b) ≫ SSet.yonedaEquiv.symm b.edge := by
  have hf := anodyneExtensionFamily_fac (horn 2 (0 : Fin 3)).ι (kanSpanHorn a b)
  change ((horn 2 (0 : Fin 3)).ι ▷ kanSpanPastingChoices a b) ≫
    kanSpanPastingFamily a b =
      fst (Λ[2, 0] : SSet.{u}) (kanSpanPastingChoices a b) ≫ kanSpanHorn a b at hf
  have he : (stdSimplex.δ 1 : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      horn₂₀.ι₀₂ ≫ (horn 2 (0 : Fin 3)).ι := (horn.ι_ι _ _ (by decide)).symm
  rw [he, comp_whiskerRight_assoc, hf, whiskerRight_fst_assoc, kanSpanHorn_target]

/-- 全選択の比較辺を同時に評価する実族。 -/
def kanSpanPastedEdgeFamily {K : SSet.{u}} {z x y : K _⦋0⦌}
    (a : K.Edge z x) (b : K.Edge z y) :
    (Δ[1] : SSet.{u}) ⊗ kanSpanPastingChoices a b ⟶ K :=
  (stdSimplex.δ 0 ▷ kanSpanPastingChoices a b) ≫ kanSpanPastingFamily a b

end SerrePositivity.KST.SConstruction
