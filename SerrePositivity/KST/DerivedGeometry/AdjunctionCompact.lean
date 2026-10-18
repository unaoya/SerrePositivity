module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：余積への射の有限和分解による compact 性を随伴で移送する。
方針：右随伴の余積比較同型と加法的 Hom 随伴を使う。
規約：余積の添字宇宙を明示し、導来随伴の存在はここでは仮定しない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の T1 の形式的部分。
-/

@[expose] public section
noncomputable section

universe u v₁ v₂ w₁ w₂

namespace SerrePositivity.KST.DerivedGeometry

open CategoryTheory Limits Preadditive

variable {C : Type w₁} [Category.{v₁} C] [Preadditive C]
  {D : Type w₂} [Category.{v₂} D] [Preadditive D]

/--
概要：指定宇宙の余積への射が有限個の成分の和に分解する対象。
方針：加法圏の Hom 上の有限和で compact 性を表す。
規約：既存 dg 加群の moduleCompact と同じ有限和の条件。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の compact 生成。
-/
def coproductCompact [HasCoproducts.{u} C] (X : C) : Prop :=
  ∀ (J : Type u) (Y : J → C) (f : X ⟶ ∐ Y),
    ∃ (t : Finset J) (g : ∀ j, X ⟶ Y j), ∑ j ∈ t, g j ≫ Sigma.ι Y j = f

/--
概要：余積を保つ右随伴の左随伴は compact 対象を保つ。
方針：随伴で移した射を余積比較同型に沿って有限和分解し、各成分を戻す。
規約：対象の幾何的生成性や導来関手の存在は要求しない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の自由係数化。
-/
lemma coproductCompact_leftAdjoint [HasCoproducts.{u} C] [HasCoproducts.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive]
    (adj : F ⊣ G) (hG : ∀ (J : Type u), PreservesColimitsOfShape (Discrete J) G)
    {X : C} (hX : coproductCompact.{u} X) : coproductCompact.{u} (F.obj X) := by
  classical
  intro J Y f
  let := hG J
  let c := sigmaComparison G Y
  obtain ⟨t, g, hg⟩ := hX J (fun j => G.obj (Y j))
    (adj.homEquiv X (∐ Y) f ≫ inv c)
  refine ⟨t, fun j => (adj.homEquiv X (Y j)).symm (g j), ?_⟩
  apply (adj.homAddEquiv X (∐ Y)).injective
  rw [map_sum]
  simp only [Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  have h := congrArg (fun k => k ≫ c) hg
  simpa only [c, sum_comp, Category.assoc, ι_comp_sigmaComparison,
    IsIso.inv_hom_id, Category.comp_id] using h

end SerrePositivity.KST.DerivedGeometry
