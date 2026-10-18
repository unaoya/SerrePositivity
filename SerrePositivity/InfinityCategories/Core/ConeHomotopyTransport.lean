module

public import SerrePositivity.InfinityCategories.Core.ConeRestrictionCocartesianEdge
public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismBoundaryExtension

/-!
概要：錐の頂点を固定した図式のホモトピーの持ち上げ。
方針：点の coslice の left fibration に図式のホモトピーを持ち上げ、join と直積の比較で錐の族へ戻す。
規約：指定した錐の頂点は区間上で厳密に定値。
使われ方：Kerodon Proposition 5.3.7.5 の錐の制限の cocartesian な辺の存在。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式のホモトピーは与えた錐から錐の頂点を固定して持ち上がる。
方針：点の coslice の left fibration の先頭端点の持ち上げを使い、join の右側の直積の比較で族にする。
規約：X は quasicategory、K は任意、初期錐と右因子上の族を厳密に固定する。
使われ方：Kerodon Proposition 5.3.7.5 の cocartesian な錐の輸送。 -/
lemma coneHomotopy_extend {K X : SSet.{u}} [Quasicategory X]
    (F₀ : join (Δ[0] : SSet.{u}) K ⟶ X)
    (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀ : SSet.ι₀ ≫ H = joinInr Δ[0] K ≫ F₀) :
    ∃ G : join (Δ[0] : SSet.{u}) K ⊗ Δ[1] ⟶ X,
      SSet.ι₀ ≫ G = F₀ ∧ (joinInr Δ[0] K ▷ Δ[1]) ≫ G = H ∧
        (joinInl Δ[0] K ▷ Δ[1]) ≫ G = fst Δ[0] Δ[1] ≫ joinInl Δ[0] K ≫ F₀ := by
  let point := joinInl (Δ[0] : SSet.{u}) K ≫ F₀
  let s₀ := sliceUnderCurry F₀ (show joinInl Δ[0] K ≫ F₀ = point from rfl)
  let q := sliceUnderProjection point
  let B := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H
  have hs₀ : s₀ ≫ q = joinInr Δ[0] K ≫ F₀ := sliceUnderCurry_projection _ _
  have := leftAnodyneExtensions_point_whiskerRight K q (LeftFibration.mem (p := q))
  have hw : CommSq (snd (horn 1 0 : SSet.{u}) K ≫ s₀) ((horn 1 0).ι ▷ K) q B := by
    constructor
    rw [Category.assoc, hs₀]
    dsimp [B]
    rw [← Category.assoc ((horn 1 0).ι ▷ K), hornOneFirst_prism_factorization,
      Category.assoc, Category.assoc]
    change snd (horn 1 0 : SSet.{u}) K ≫ (joinInr Δ[0] K ≫ F₀) =
      snd (horn 1 0 : SSet.{u}) K ≫ (SSet.ι₀ ≫ H)
    rw [h₀]
  let L := hw.lift
  have hL₀ : prismEndpoint 0 K ≫ L = s₀ := by
    have hh := congrArg (fun t ↦ hornOneFirstSection K ≫ t) hw.fac_left
    simpa only [← Category.assoc, hornOneFirstSection_ι, hornOneFirstSection_snd,
      Category.id_comp] using hh
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = s₀ := by
    dsimp [R]
    rw [← prismEndpoint_zero_braiding K, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) K).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₀
  have hRq : R ≫ q = H := by
    dsimp [R, L]
    rw [Category.assoc, hw.fac_right]
    dsimp [B]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  let G := joinTensorRight (Δ[0] : SSet.{u}) K Δ[1] ≫ sliceUnderUncurry R
  refine ⟨G, ?_, ?_, ?_⟩
  · dsimp [G]
    rw [← Category.assoc, joinTensorRight_ι₀, ← sliceUnderUncurry_precomp, hR₀,
      sliceUnderUncurry_curry]
  · dsimp [G]
    rw [← Category.assoc, joinTensorRight_inr, sliceUnderUncurry_projection]
    exact hRq
  · dsimp [G]
    rw [← Category.assoc, joinTensorRight_inl, Category.assoc, sliceUnderUncurry_fixed]

end SerrePositivity.InfinityCategories
