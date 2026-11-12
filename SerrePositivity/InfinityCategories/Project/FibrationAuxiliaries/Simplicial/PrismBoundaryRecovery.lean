module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.PrismBoundaryData

/-!
概要：相対内部 Hom の境界データから実際の prism の二端点と底を回収する。
方針：二射影の等式を uncurry して区間境界で制限する。
規約：全パラメーターに対する厳密な等式。
使われ方：同時端点制限のホーンの相対充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：二端点と底のデータは実際の prism の相対制限で表示できる。
方針：二射影を uncurry して境界制限と底の式を使う。
規約：prism の存在は等式の表示にのみ用いる。
使われ方：既定のホーン上の相対内部 Hom の可換性。 -/
lemma prismBoundaryData_eq_of_prism {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ)
    (H : Δ[1] ⊗ (K ⊗ L) ⟶ E)
    (H₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = v₀) (H₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = v₁)
    (Hp : H ≫ p = δ) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r v₀ v₁ δ h₀ h₁ = curry ((α_ Δ[1] K L).hom ≫ H) ≫ r.π := by
  apply r.hom_ext
  · rw [Category.assoc, r.π_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_fst]
    simp only [internalHom, Quiver.Hom.unop_op]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    change (α_ (boundary 1 : SSet.{u}) K L).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram v₀ v₁ =
      (α_ (boundary 1 : SSet.{u}) K L).hom ≫ ((boundary 1).ι ▷ (K ⊗ L)) ≫ H
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict, H₀, H₁]
  · rw [Category.assoc, r.π_snd, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_snd]
    apply uncurry_injective
    change uncurry (curry _) = uncurry (curry _ ≫ (ihom (Δ[1] ⊗ K)).map p)
    rw [uncurry_natural_right, uncurry_curry, uncurry_curry, Category.assoc, Hp]

/-- 概要：二端点のデータを持つ lift の評価の境界は指定した二射の図式。
方針：第一射影を uncurry して結合子の逆を合成する。
規約：底の条件も含む相対データの等式から結論する。
使われ方：充填した prism の二端点を厳密に回収する。 -/
lemma prismBoundaryData_recover_boundary {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ)
    (F : L ⟶ (ihom (Δ[1] ⊗ K)).obj E)
    (hF : F ≫ r.π = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r v₀ v₁ δ h₀ h₁) :
    ((boundary 1).ι ▷ (K ⊗ L)) ≫ ((α_ Δ[1] K L).inv ≫ uncurry F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram v₀ v₁ := by
  have h := congrArg (fun w ↦ w ≫ r.fst) hF
  rw [Category.assoc, r.π_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_fst] at h
  change F ≫ (pre ((boundary 1).ι ▷ K)).app E = _ at h
  have hh := congrArg (fun w ↦ (α_ (boundary 1 : SSet.{u}) K L).inv ≫ uncurry w) h
  rw [uncurry_pre_app, uncurry_curry, Iso.inv_hom_id_assoc] at hh
  exact hh

/-- 概要：二端点のデータを持つ lift の評価の底は指定した prism。
方針：第二射影を uncurry して結合子の逆を合成する。
規約：底の射を同型まで弱めない。
使われ方：充填した prism が指定した区間族を覆うこと。 -/
lemma prismBoundaryData_recover_base {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ)
    (F : L ⟶ (ihom (Δ[1] ⊗ K)).obj E)
    (hF : F ≫ r.π = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r v₀ v₁ δ h₀ h₁) :
    ((α_ Δ[1] K L).inv ≫ uncurry F) ≫ p = δ := by
  have h := congrArg (fun w ↦ w ≫ r.snd) hF
  rw [Category.assoc, r.π_snd, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_snd] at h
  change F ≫ (ihom (Δ[1] ⊗ K)).map p = _ at h
  have hh := congrArg (fun w ↦ (α_ Δ[1] K L).inv ≫ uncurry w) h
  rw [uncurry_natural_right, uncurry_curry, Iso.inv_hom_id_assoc] at hh
  exact hh

/-- 概要：二端点の相対データはパラメーターの制限に自然。
方針：二射影を curry の自然性と境界図式の自然性で比較する。
規約：パラメーター射は任意。
使われ方：既定のホーン上での相対持ち上げ問題を作る。 -/
lemma prismBoundaryData_precomp {E B K L M : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ) (g : M ⟶ L) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r v₀ v₁ δ h₀ h₁ =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r ((K ◁ g) ≫ v₀) ((K ◁ g) ≫ v₁)
        ((Δ[1] ◁ (K ◁ g)) ≫ δ)
        (by rw [Category.assoc, h₀]; simpa only [Category.assoc] using
          congrArg (fun w ↦ w ≫ δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 (K ◁ g)).symm)
        (by rw [Category.assoc, h₁]; simpa only [Category.assoc] using
          congrArg (fun w ↦ w ≫ δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1 (K ◁ g)).symm) := by
  apply r.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_fst, ← curry_natural_left]
    congr 1
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_snd, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_snd, ← curry_natural_left]
    congr 1

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
