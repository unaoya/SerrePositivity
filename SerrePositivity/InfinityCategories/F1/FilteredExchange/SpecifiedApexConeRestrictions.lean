module
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpecifiedApexLimitConeTransport


/-!
概要：指定された極限錐の輸送の二つの制限を明示する。
方針：境界の等式を左右の包含へ制限して prism の貼り合わせを計算する。
規約：頂点側は元の指定 prism、図式側は定値。
使われ方：Cat_∞ の引き戻し錐の二射影の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：輸送の全錐のホモトピーは頂点側で指定 prism。
方針：二因子の和への制限を左包含へ制限する。
規約：全時刻の厳密な等式。
使われ方：元の比較の辺自体を錐頂点で回収する。 -/
lemma SpecifiedApexLimitConeTransport.apex {K X : SSet.{u}} {p : K ⟶ X}
    {a : (Δ[0] : SSet.{u}) ⟶ X}
    {P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X} {d : JoinCone p}
    (t : SpecifiedApexLimitConeTransport d a P) :
    (joinInl (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ t.homotopy.h =
      (β_ (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ P := by
  have h := congrArg
    (fun z ↦ ((coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ z)
    t.boundary
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc] at h
  calc
    _ = _ := h
    _ = (β_ (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] ◁ (coprod.inl : Δ[0] ⟶ Δ[0] ⨿ K)) ≫ apexConeBoundaryPrism p P) := rfl
    _ = _ := by rw [apexConeBoundaryPrism, coprodPrism_inl]
/-- 概要：輸送の全錐のホモトピーは図式側で定値。
方針：二因子の和への制限を右包含へ制限する。
規約：元の図式を全時刻で固定する。
使われ方：二脚の自然性の正方形の成分を計算する。 -/
lemma SpecifiedApexLimitConeTransport.diagram {K X : SSet.{u}} {p : K ⟶ X}
    {a : (Δ[0] : SSet.{u}) ⟶ X}
    {P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X} {d : JoinCone p}
    (t : SpecifiedApexLimitConeTransport d a P) :
    (joinInr (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ t.homotopy.h =
      fst K (Δ[1] : SSet.{u}) ≫ p := by
  have h := congrArg
    (fun z ↦ ((coprod.inr : K ⟶ (Δ[0] : SSet.{u}) ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ z)
    t.boundary
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc] at h
  calc
    _ = _ := h
    _ = (β_ K (Δ[1] : SSet.{u})).hom ≫
        ((Δ[1] ◁ (coprod.inr : K ⟶ Δ[0] ⨿ K)) ≫ apexConeBoundaryPrism p P) := rfl
    _ = _ := by rw [apexConeBoundaryPrism, coprodPrism_inr]; rfl

end SerrePositivity.InfinityCategories.F2
