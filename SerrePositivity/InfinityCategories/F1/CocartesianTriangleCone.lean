module

public import SerrePositivity.InfinityCategories.F1.CosliceConeExtension

/-!
概要：cocartesian な後半の辺を持つ三角形の錐の延長。
方針：後半の辺の錐を延長し、二辺を内ホーン上で貼り、内 anodyne な join を充填する。
規約：最初の辺は δ₂、後半の辺は δ₀、長辺は δ₁。
使われ方：Kerodon Corollary 5.1.2.4、Proposition 5.2.5.1 の transport の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：後半の辺が cocartesian な三角形の錐を最初の辺の錐から延長する。
方針：後半の辺の始点への相対制限で錐を延長し、内ホーンとの join を充填する。
規約：指定された部分パラメーターの錐と底の錐を厳密に保つ。
使われ方：Kerodon Corollary 5.1.2.4、三角形から最初の辺への相対制限。 -/
lemma cocartesianTriangle_extendCone {X Y A : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (A₀ : A.Subcomplex) (G : join (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ⟶ X)
    (H : join (Δ[1] : SSet.{u}) A ⟶ X) (B : join (Δ[2] : SSet.{u}) A ⟶ Y)
    (hG : joinInl _ _ ≫ G = t)
    (hH : joinInl _ _ ≫ H = stdSimplex.δ (2 : Fin 3) ≫ t)
    (hB : joinInl _ _ ≫ B = t ≫ q)
    (hGH : joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 _) A₀.ι ≫ H)
    (hGq : G ≫ q = joinMap (𝟙 _) A₀.ι ≫ B)
    (hHq : H ≫ q = joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ B) :
    ∃ T : join (Δ[2] : SSet.{u}) A ⟶ X, joinInl _ _ ≫ T = t ∧
      joinMap (𝟙 _) A₀.ι ≫ T = G ∧
      joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ T = H ∧ T ≫ q = B := by
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (0 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  let G₁ := joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G
  let H₁ := joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ H
  let B₁ := joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 A) ≫ B
  have hG₁ : joinInl _ _ ≫ G₁ = stdSimplex.δ (0 : Fin 3) ≫ t := by
    dsimp only [G₁]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, hG]
  have hH₁ : joinInl _ _ ≫ H₁ =
      stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ t) := by
    dsimp only [H₁]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, hH]
    rw [← Category.assoc, ← hv, Category.assoc]
  have hB₁ : joinInl _ _ ≫ B₁ = (stdSimplex.δ (0 : Fin 3) ≫ t) ≫ q := by
    dsimp only [B₁]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, hB, Category.assoc]
  have hGH₁ : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (A₀ : SSet.{u})) ≫ G₁ =
      joinMap (𝟙 _) A₀.ι ≫ H₁ := by
    have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (0 : Fin 2))
      (𝟙 (A₀ : SSet.{u})) ≫ z) hGH
    simpa only [G₁, H₁, ← Category.assoc, ← joinMap_comp, Category.comp_id,
      Category.id_comp, hv] using h
  have hGq₁ : G₁ ≫ q = joinMap (𝟙 _) A₀.ι ≫ B₁ := by
    have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (0 : Fin 3))
      (𝟙 (A₀ : SSet.{u})) ≫ z) hGq
    simpa only [G₁, B₁, ← Category.assoc, ← joinMap_comp, Category.comp_id,
      Category.id_comp] using h
  have hHq₁ : H₁ ≫ q = joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A) ≫ B₁ := by
    have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ z) hHq
    simpa only [H₁, B₁, ← Category.assoc, ← joinMap_comp, Category.comp_id,
      Category.id_comp, hv] using h
  have := relativeCosliceRestriction_source_of_isCocartesianEdge
    (stdSimplex.δ (0 : Fin 3) ≫ t) q he
  obtain ⟨J, hJ, hJb, hJs, hJq⟩ := relativeCosliceRestriction_extendCone
    (stdSimplex.δ (0 : Fin 3) ≫ t) q (stdSimplex.δ (1 : Fin 2)) A₀
    G₁ H₁ B₁ hG₁ hH₁ hB₁ hGH₁ hGq₁ hHq₁
  let hs := joinLeft_horn₂₁_isPushout A
  let W := hs.desc H J hJs.symm
  have hWb : joinMap (𝟙 (horn 2 1 : SSet.{u})) A₀.ι ≫ W =
      joinMap (horn 2 1).ι (𝟙 (A₀ : SSet.{u})) ≫ G := by
    apply (joinLeft_horn₂₁_isPushout (A₀ : SSet.{u})).hom_ext
    · have h := congrArg (fun z ↦ joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inl_desc H J hJs.symm)
      have hh := h.trans hGH.symm
      simpa only [← Category.assoc, ← joinMap_comp, Category.comp_id, Category.id_comp,
        horn.ι_ι] using hh
    · have h := congrArg (fun z ↦ joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inr_desc H J hJs.symm)
      have hh := h.trans hJb
      simpa only [G₁, ← Category.assoc, ← joinMap_comp, Category.comp_id,
        Category.id_comp, horn.ι_ι] using hh
  have hWq : W ≫ q = joinMap (horn 2 1).ι (𝟙 A) ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc]
      simpa only [← Category.assoc, ← joinMap_comp, Category.comp_id, horn.ι_ι] using hHq
    · rw [← Category.assoc, hs.inr_desc]
      simpa only [B₁, ← Category.assoc, ← joinMap_comp, Category.comp_id,
        horn.ι_ι] using hJq
  let hu := joinUnion_isPushout (horn 2 1) A₀
  let V := hu.desc W G hWb
  have hVq : V ≫ q = (joinUnion (horn 2 1) A₀).ι ≫ B := by
    apply hu.hom_ext
    · rw [← Category.assoc, hu.inl_desc, ← Category.assoc, joinUnionLeft_ι]
      exact hWq
    · rw [← Category.assoc, hu.inr_desc, ← Category.assoc, joinUnionRight_ι]
      exact hGq
  have hinner := rightAnodyneExtensions_horn (1 : Fin 3) (by decide)
  have := joinUnion_innerAnodyne_of_rightAnodyne (horn 2 1) A₀ hinner q InnerFibration.mem
  let sq : CommSq V (joinUnion (horn 2 1) A₀).ι q B := ⟨hVq⟩
  have hleft : joinMap (horn 2 1).ι (𝟙 A) ≫ sq.lift = W := by
    rw [← joinUnionLeft_ι, Category.assoc, sq.fac_left]
    exact hu.inl_desc _ _ _
  have hright : joinMap (𝟙 (Δ[2] : SSet.{u})) A₀.ι ≫ sq.lift = G := by
    rw [← joinUnionRight_ι, Category.assoc, sq.fac_left]
    exact hu.inr_desc _ _ _
  refine ⟨sq.lift, ?_, hright, ?_, sq.fac_right⟩
  · have h := congrArg (fun z ↦ joinInl (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans hG
  · rw [← horn.ι_ι (i := (1 : Fin 3)) (j := (2 : Fin 3)) (hij := by decide)]
    rw [← Category.comp_id (𝟙 A),
      joinMap_comp horn₂₁.ι₀₁ (horn 2 1).ι (𝟙 A) (𝟙 A), Category.assoc, hleft]
    exact hs.inl_desc _ _ _

end SerrePositivity.InfinityCategories
