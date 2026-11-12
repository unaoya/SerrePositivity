module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport

/-!
概要：inner fibration に沿う合成可能な二つの prism の三角形への延長。
方針：二辺の pushout を積関手で写し、内ホーンとパラメーターの積を充填する。
規約：底の三角形の族を厳密に固定する。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、transport 関手の合成の証人。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：終点包含とパラメーターの積は prism の終点を経由する。
方針：標準区間の δ₀ を終点への定値射と書く。
規約：始域の標準単体は Δ[0]。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、二つの prism の共通端点。 -/
lemma trianglePrism_endpoint_one (A : SSet.{u}) :
    ((stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A := by
  rw [stdSimplex.δ_zero_eq_const]
  rfl

/-- 概要：始点包含とパラメーターの積は prism の始点を経由する。
方針：標準区間の δ₁ を始点への定値射と書く。
規約：始域の標準単体は Δ[0]。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、二つの prism の共通端点。 -/
lemma trianglePrism_endpoint_zero (A : SSet.{u}) :
    ((stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 概要：合成可能な二つの prism を底の三角形の族に沿って延長する。
方針：内ホーンの pushout に貼り、積を取った内 anodyne 包含を持ち上げる。
規約：prism の共通端点での一致は厳密な等式。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、transport の合成の三角形。 -/
lemma innerFibration_fillTrianglePrism {X B A : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] (H₀₁ H₁₂ : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (b : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
    (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H₀₁ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H₁₂)
    (h₀₁ : H₀₁ ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ b)
    (h₁₂ : H₁₂ ≫ p = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ b) :
    ∃ T : (Δ[2] : SSet.{u}) ⊗ A ⟶ X,
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T = H₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T = H₁₂ ∧ T ≫ p = b := by
  let hs := horn₂₁.isPushout.map (tensorRight A)
  have hw' : (stdSimplex.δ (0 : Fin 2) ▷ A) ≫ H₀₁ =
      (stdSimplex.δ (1 : Fin 2) ▷ A) ≫ H₁₂ := by
    rw [trianglePrism_endpoint_one, trianglePrism_endpoint_zero, Category.assoc,
      Category.assoc, hw]
  let H := hs.desc H₀₁ H₁₂ hw'
  have hHp : H ≫ p = ((horn 2 1).ι ▷ A) ≫ b := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc]
      change H₀₁ ≫ p = (horn₂₁.ι₀₁ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ b
      simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using h₀₁
    · rw [← Category.assoc, hs.inr_desc]
      change H₁₂ ≫ p = (horn₂₁.ι₁₂ ▷ A) ≫ ((horn 2 1).ι ▷ A) ≫ b
      simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using h₁₂
  have := (innerAnodyneExtensions.horn_ι (show 0 < (1 : Fin 3) by decide)
    (show (1 : Fin 3) < Fin.last 2 by decide)).whiskerRight A p InnerFibration.mem
  let sq : CommSq H ((horn 2 1).ι ▷ A) p b := ⟨hHp⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide), comp_whiskerRight,
      Category.assoc, sq.fac_left]
    exact hs.inl_desc _ _ _
  · rw [← horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide), comp_whiskerRight,
      Category.assoc, sq.fac_left]
    exact hs.inr_desc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
