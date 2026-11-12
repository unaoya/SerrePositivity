module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Objects
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension

/-!
概要：left fibration に沿う、境界と始点を固定した prism の持ち上げ。
方針：一次の左ホーンと境界の積の和が left anodyne であることを使う。
規約：底の全 prism を厳密に固定し、全ての次元を扱う。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の left fibration の場合の準備。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：left fibration は標準 prism の境界と始点を固定して持ち上げられる。
方針：pushout で二つの制限を貼り、left anodyne な積の和の rlp を使う。
規約：n=0 も含み、底や全空間に quasicategory 性を仮定しない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、Lemma 5.2.2.13（Tag 02RB） の left fibration 版。 -/
lemma leftFibration_lift_boundary_prism {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ X)
    (F₀ : (Δ[n] : SSet.{u}) ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ B)
    (hF₀ : (boundary n).ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary n : SSet.{u}) ≫ H)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ b)
    (hb : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ X,
      (Δ[1] ◁ (boundary n).ι) ≫ F = H ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ F = F₀ ∧ F ≫ p = b := by
  let S := horn.{u} 1 0
  let T := boundary.{u} n
  let hs := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n] ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := hs.desc H (snd (S : SSet.{u}) Δ[n] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := hs.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n] ≫ F₀ := hs.inr_desc _ _ _
  have hap : a ≫ p = (Subcomplex.unionProd S T).ι ≫ b := by
    apply hs.hom_ext
    · rw [← Category.assoc, ha₁, hH, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, ha₂, Category.assoc, hb, ← Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization,
        ← Category.assoc (Subcomplex.unionProd.ι₂ S T) (Subcomplex.unionProd S T).ι b,
        Subcomplex.unionProd.ι₂_ι]
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_unionProd.{u} (0 : Fin 1) n
  have : HasLiftingProperty (Subcomplex.unionProd S T).ι p :=
    hi p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
  let sq : CommSq a (Subcomplex.unionProd S T).ι p b := ⟨hap⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, sq.fac_left, ha₁]
  · have h : (S.ι ▷ (Δ[n] : SSet.{u})) ≫ sq.lift =
        snd (S : SSet.{u}) Δ[n] ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, sq.fac_left, ha₂]
    have h' := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection (Δ[n] : SSet.{u}) ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
