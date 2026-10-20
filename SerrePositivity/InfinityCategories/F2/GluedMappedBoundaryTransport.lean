module

public import SerrePositivity.InfinityCategories.F2.MappedBoundaryFiberTransport
public import SerrePositivity.InfinityCategories.F2.GluedFiberDetection

/-!
概要：共通の元の境界と二つの有限模型を、同じ fiber へ全円柱を保って輸送する。
方針：底を有限 pushout で貼り、境界を先に輸送してから両模型へ相対延長する。
規約：境界の像の円柱を厳密に保持。使われ方：任意の Kan 二入力の相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通の境界の輸送を保つ、二つの有限模型の同時輸送。
方針：一つの底収縮と境界輸送の二つの相対延長。
規約：元の境界の全円柱。使われ方：標的二入力を元の二入力へ移す。 -/
lemma leftFibration_glued_mapped_boundary_transport {A K L R E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : R ⟶ B) [LeftFibration p] (q : E ⟶ B) [LeftFibration q]
    (r : D ⟶ B) [LeftFibration r] (c : R ⟶ E) (d : R ⟶ D)
    (hc : c ≫ q = p) (hd : d ≫ r = p)
    (i : A ⟶ K) [Mono i] (j : A ⟶ L) [Mono j]
    (a : A ⟶ R) (f : K ⟶ E) (g : L ⟶ D)
    (hf : i ≫ f = a ≫ c) (hg : j ≫ g = a ≫ d) :
    ∃ b : B _⦋0⦌, ∃ t : A ⟶ vertexFiber p b,
      ∃ s : K ⟶ vertexFiber q b, ∃ v : L ⟶ vertexFiber r b,
      i ≫ s = t ≫ vertexFiberMap p q c hc b ∧
      j ≫ v = t ≫ vertexFiberMap p r d hd b ∧
      ∃ T : SSet.Homotopy a (t ≫ vertexFiberι p b),
      ∃ U : SSet.Homotopy f (s ≫ vertexFiberι q b),
      ∃ V : SSet.Homotopy g (v ≫ vertexFiberι r b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = T.h ≫ c ∧
        (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = T.h ≫ d := by
  have hb : i ≫ f ≫ q = j ≫ g ≫ r := by
    rw [← Category.assoc, hf, Category.assoc, hc,
      ← Category.assoc, hg, Category.assoc, hd]
  have := finite_pushout i j
  let e := pushout.desc (f ≫ q) (g ≫ r) hb
  obtain ⟨b, ⟨H⟩⟩ := exists_nullHomotopy_of_isFilteredInfinity e
  let Hf : SSet.Homotopy (f ≫ q) (SSet.const b : K ⟶ B) :=
    { h := (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inl_desc _ _ _
      h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
      rel := (functorHomotopyPrecomp H (pushout.inl i j)).rel }
  let Hg : SSet.Homotopy (g ≫ r) (SSet.const b : L ⟶ B) :=
    { h := (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; exact pushout.inr_desc _ _ _
      h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
      rel := (functorHomotopyPrecomp H (pushout.inr i j)).rel }
  let Ha : SSet.Homotopy (a ≫ p) (SSet.const b : A ⟶ B) :=
    { h := (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h
      h₀ := by
        change SSet.ι₀ ≫ (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h = a ≫ p
        rw [SSet.ι₀_comp_assoc, Hf.h₀, ← Category.assoc, hf, Category.assoc, hc]
      h₁ := by
        change SSet.ι₁ ≫ (i ▷ (Δ[1] : SSet.{u})) ≫ Hf.h = SSet.const b
        rw [SSet.ι₁_comp_assoc, Hf.h₁, SSet.comp_const]
      rel := (functorHomotopyPrecomp Hf i).rel }
  obtain ⟨t, T, hT⟩ := leftFibration_transport_along_nullHomotopy p a b Ha
  obtain ⟨s, hs, U, hU, _⟩ := leftFibration_transport_mapped_boundary
    p q c hc i a f hf b Hf t T hT
  have hT' : T.h ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ Hg.h := by
    rw [hT]
    change (i ▷ (Δ[1] : SSet.{u})) ≫
      (pushout.inl i j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        (j ▷ (Δ[1] : SSet.{u})) ≫ (pushout.inr i j ▷ (Δ[1] : SSet.{u})) ≫ H.h
    rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, pushout.condition]
  obtain ⟨v, hv, V, hV, _⟩ := leftFibration_transport_mapped_boundary
    p r d hd j a g hg b Hg t T hT'
  exact ⟨b, t, s, v, hs, hv, T, U, V, hU, hV⟩

end SerrePositivity.InfinityCategories.F2
