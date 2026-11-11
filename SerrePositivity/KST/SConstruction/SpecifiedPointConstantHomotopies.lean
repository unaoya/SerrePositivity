module
public import SerrePositivity.KST.SConstruction.MappingSquareCornerIdentities
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 指定頂点の元の辺で定数端点を合わせる
概要：定数端点の実円柱を、指定頂点で保持する元の辺の端点へ厳密に合わせる。
方針：指定全区間の零・一時刻で両端を照合し、元の円柱は変更しない。
規約：端点の存在を仮定せず、指定区間の全時刻の等号から導く。
使われ方：共通パラメータ上の三つの元の適合円柱の端点を合わせる。
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

/-- 定数端点の円柱を前後合成し、元の全区間と定数端点を保持する。 -/
def constantFamilyHomotopyWhisker {P Q E B : SSet.{u}} (p : P ⟶ Q) (m : E ⟶ B)
    {a b : E _⦋0⦌} (H : SSet.Homotopy (SSet.const (X := Q) a) (SSet.const b)) :
    SSet.Homotopy (SSet.const (X := P) (m.app _ a)) (SSet.const (m.app _ b)) where
  h := (p ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ m
  h₀ := by
    change SSet.ι₀ ≫ (p ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ m = SSet.const (m.app _ a)
    rw [SSet.ι₀_comp_assoc, H.h₀_assoc, SSet.const_comp, SSet.comp_const]
  h₁ := by
    change SSet.ι₁ ≫ (p ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ m = SSet.const (m.app _ b)
    rw [SSet.ι₁_comp_assoc, H.h₁_assoc, SSet.const_comp, SSet.comp_const]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 前後合成後も、指定した一点で元の全区間を同じ後合成として回収する。 -/
lemma constantFamilyHomotopyWhisker_boundary {P Q E B : SSet.{u}}
    (p : P ⟶ Q) (m : E ⟶ B) {a b : E _⦋0⦌}
    (H : SSet.Homotopy (SSet.const (X := Q) a) (SSet.const b))
    (j : (Δ[0] : SSet.{u}) ⟶ P) (k : (Δ[0] : SSet.{u}) ⟶ Q)
    (v : (Δ[1] : SSet.{u}) ⟶ E) (hp : j ≫ p = k)
    (hv : (k ▷ (Δ[1] : SSet.{u})) ≫ H.h = snd (Δ[0] : SSet.{u}) Δ[1] ≫ v) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (constantFamilyHomotopyWhisker p m H).h =
      snd (Δ[0] : SSet.{u}) Δ[1] ≫ v ≫ m := by
  simp only [constantFamilyHomotopyWhisker, ← Category.assoc]
  rw [← comp_whiskerRight, hp, hv, Category.assoc]

/-- 元の指定全区間から、円柱の両端と元の辺の端点が等しいことを導く。 -/
lemma constantHomotopy_endpoints_of_specifiedPoint {P E : SSet.{u}}
    {a b x y : E _⦋0⦌} (H : SSet.Homotopy (SSet.const (X := P) a) (SSet.const b))
    (j : (Δ[0] : SSet.{u}) ⟶ P) (e : E.Edge x y)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) :
    a = x ∧ b = y := by
  have h₀ := congrArg (fun k => SSet.ι₀ ≫ k) h
  have h₁ := congrArg (fun k => SSet.ι₁ ≫ k) h
  rw [SSet.ι₀_comp_assoc, H.h₀, SSet.comp_const, ← Category.assoc, SSet.ι₀_snd,
    ← stdSimplex.δ_one_eq_const, SSet.Edge.δ_one_yonedaEquiv_symm] at h₀
  rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const, ← Category.assoc, SSet.ι₁_snd,
    ← stdSimplex.δ_zero_eq_const, SSet.Edge.δ_zero_yonedaEquiv_symm] at h₁
  exact ⟨by simpa only [SSet.yonedaEquiv_const, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₀,
    by simpa only [SSet.yonedaEquiv_const, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₁⟩

/-- 両端だけを元の指定辺に合わせ、元の全円柱そのものを保持する。 -/
def specifiedPointConstantHomotopy {P E : SSet.{u}}
    {a b x y : E _⦋0⦌} (H : SSet.Homotopy (SSet.const (X := P) a) (SSet.const b))
    (j : (Δ[0] : SSet.{u}) ⟶ P) (e : E.Edge x y)
    (h : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) :
    SSet.Homotopy (SSet.const (X := P) x) (SSet.const y) where
  h := H.h
  h₀ := H.h₀.trans (congrArg SSet.const (constantHomotopy_endpoints_of_specifiedPoint H j e h).1)
  h₁ := H.h₁.trans (congrArg SSet.const (constantHomotopy_endpoints_of_specifiedPoint H j e h).2)
  rel := H.rel

end SerrePositivity.KST.SConstruction
