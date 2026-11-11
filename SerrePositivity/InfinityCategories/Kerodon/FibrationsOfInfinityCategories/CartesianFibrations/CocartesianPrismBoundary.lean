module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPrismExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension

/-!
概要：cocartesian な垂直辺を持つ境界の prism の相対延長。
方針：先頭の単体と境界の prism を貼り、cocartesian な prism の充填を適用する。
規約：基底の prism と先頭の単体を厳密に固定する。
使われ方：Kerodon §5.1.1（Tag 01T4）・§7.1.5（Tag 02WE） の輸送の持ち上げ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：先頭の単体と境界の prism は cocartesian な最初の垂直辺の下で基底上へ延長する。
方針：pushout で二つの射を貼り、prism の相対充填から両制限を回収する。
規約：quasicategory 性は不要、p は inner fibration。
使われ方：Kerodon §5.1.1（Tag 01T4）・§7.1.5（Tag 02WE） の輸送の存在の境界テスト。 -/
lemma prism_lift_boundary_with_endpoint {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ E)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ β)
    (hF₀p : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ β)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ F = F₀ ∧ F ≫ p = β := by
  let S := horn.{u} 1 0
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := q.desc H (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := q.inr_desc _ _ _
  have hv : a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩ =
        H.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋1⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n)
    change a.app (Opposite.op ⦋1⦌)
      ((Subcomplex.unionProd.ι₁ S T).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n)) = _ at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge_ι₁] at h
    exact h
  have hap : a ≫ p = (Subcomplex.unionProd S T).ι ≫ β := by
    apply q.hom_ext
    · rw [← Category.assoc, ha₁, hHp, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, ha₂, Category.assoc, hF₀p,
        ← Category.assoc (Subcomplex.unionProd.ι₂ S T), Subcomplex.unionProd.ι₂_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc]
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prism_exists_lift_of_cocartesian_firstEdge p n a β hap
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p hv).2 hH)
  refine ⟨F, ?_, ?_, hFp⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h : (S.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F =
        snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
    have h' := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection (Δ[n + 1] : SSet.{u}) ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
