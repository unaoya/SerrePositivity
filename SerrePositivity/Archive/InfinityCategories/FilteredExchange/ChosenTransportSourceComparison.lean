module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportSourceIdentity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberTransportFamilySourceComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoLeftIdentityFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyConstantComponent

/-!
概要：元の選択済み輸送族の恒等初期係数での比較から、余分な自己比較を除く。
方針：元の恒等前合成を厳密に戻し、指定自己比較の恒等性を適用する。
規約：普遍輸送を再選択しない。使われ方：指定一点区間と全区間普遍輸送の橋渡し。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
local notation "T" => fiberTransportFamily p (𝟙 (vertexFiber p a)) γ h₀ h₁

/-- 元の選択済み輸送族の恒等初期値での比較は、元の全区間への直接比較と同じ値。 -/
lemma chosenTransport_parametrizedSource_heq_direct :
    HEq (FiberTransportFamily.mapIso_parametrizedSource p (𝟙 _) γ h₀ h₁ T)
      (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T) := by
  let U₁ := (T).precomposeSource (𝟙 (vertexFiber p a))
  let U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ :=
    ⟨U₁.endpoint, U₁.prism, by simpa only [Category.comp_id] using U₁.start,
      U₁.finish, U₁.over_base⟩
  have hU : U = T := fiberTransportFamily_eq_of_prism p (𝟙 _) γ U T
    (fiberTransportFamily_precomposeSource_id_prism T)
  let q := (pre (𝟙 (vertexFiber p a))).app (vertexFiber p b)
  let k := intervalMappingCurryOfEndpoints γ h₀ h₁
  let E := FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T
  have hm : U.map = (T).map ≫ q := FiberTransportFamily.precomposeSource_map T (𝟙 _)
  let e₁ := Eq.mp (congrArg (fun g ↦ FunctorIso (FiberTransportFamily.map T) g) hm)
    (FiberTransportFamily.mapIso p (𝟙 _) γ h₁ T U)
  let e₂ := Eq.mp (congrArg (fun g ↦ FunctorIso (FiberTransportFamily.map T ≫ q) g)
    (Category.assoc k (parametrizedFiberTransport p a b) q)) (E.postcomp q)
  have hcast {α β : Sort (u + 1)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  have hq : q = 𝟙 _ := by simp only [q, pre_id, NatTrans.id_app]
  have ht : (T).map = (T).map ≫ q := by rw [hq, Category.comp_id]
  have hr : HEq (FiberTransportFamily.mapIso p (𝟙 _) γ h₁ T U)
      (Iso.refl (SSet.HomotopyCategory.mk (functorVertex (T).map))) := by
    rw [hU, fiberTransportFamily_mapIso_refl p (𝟙 _) γ h₁ T]
  have he₁ : HEq e₁
      (Iso.refl (SSet.HomotopyCategory.mk (functorVertex ((T).map ≫ q)))) :=
    (hcast _ _).trans (hr.trans (iso_refl_heq_of_eq
      (congrArg SSet.HomotopyCategory.mk (congrArg functorVertex ht))))
  have he₂ : HEq e₂ E := by
    refine (hcast _ _).trans ?_
    rw [hq, functorIso_postcomp_id]
  unfold FiberTransportFamily.mapIso_parametrizedSource
  change HEq (e₁ ≪≫ e₂) E
  exact (vertexIso_trans_heq_of_left_refl e₁ e₂ (congrArg functorVertex ht) he₁).trans he₂

end SerrePositivity.InfinityCategories.F2
