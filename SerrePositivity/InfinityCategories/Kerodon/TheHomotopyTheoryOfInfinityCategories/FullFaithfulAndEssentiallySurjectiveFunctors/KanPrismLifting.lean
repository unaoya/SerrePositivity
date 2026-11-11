module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberwiseHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension

/-!
概要：Fibration に沿う相対的な prism の延長。
方針：先頭と部分複体上の prism を貼り、anodyne な積の和の rlp を使う。
規約：標的の全 prism の図式を厳密に固定する。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の境界充填。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：Fibration は始点と部分複体上の prism を固定して標的の prism を持ち上げる。
方針：先頭の一次ホーンと部分複体の pushout-product の anodyne 性を使う。
規約：全ての単体集合の部分複体をパラメーターとする。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の相対的なホモトピー延長。 -/
lemma fibration_lift_prism {A E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    (A₀ : A.Subcomplex) (H : (Δ[1] : SSet.{u}) ⊗ (A₀ : SSet.{u}) ⟶ E)
    (F₀ : A ⟶ E) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hF₀ : A₀.ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A₀ : SSet.{u}) ≫ H)
    (hH : H ≫ q = (Δ[1] ◁ A₀.ι) ≫ b)
    (hb : F₀ ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      (Δ[1] ◁ A₀.ι) ≫ F = H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ q = b := by
  let S := horn.{u} 1 0
  let hs := Subcomplex.unionProd.isPushout S A₀
  have hw : (S.ι ▷ (A₀ : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ A₀.ι) ≫ (snd (S : SSet.{u}) A ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := hs.desc H (snd (S : SSet.{u}) A ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S A₀ ≫ a = H := hs.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S A₀ ≫ a = snd (S : SSet.{u}) A ≫ F₀ := hs.inr_desc _ _ _
  have haq : a ≫ q = (Subcomplex.unionProd S A₀).ι ≫ b := by
    apply hs.hom_ext
    · rw [← Category.assoc, ha₁, hH, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, ha₂, Category.assoc, hb, ← Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization,
        ← Category.assoc (Subcomplex.unionProd.ι₂ S A₀) (Subcomplex.unionProd S A₀).ι b,
        Subcomplex.unionProd.ι₂_ι]
  have hi := anodyneExtensions_unionProd_ι' S A₀ (anodyneExtensions.horn_ι (0 : Fin 2))
  have := hi q ((HomotopicalAlgebra.fibration_iff q).mp inferInstance)
  let sq : CommSq a (Subcomplex.unionProd S A₀).ι q b := ⟨haq⟩
  let F := sq.lift
  have hF : (Subcomplex.unionProd S A₀).ι ≫ F = a := sq.fac_left
  refine ⟨F, ?_, ?_, sq.fac_right⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S A₀, Category.assoc, hF, ha₁]
  · have h : (S.ι ▷ A) ≫ F = snd (S : SSet.{u}) A ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S A₀, Category.assoc, hF, ha₂]
    have h' := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection A ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
