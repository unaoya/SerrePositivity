module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.CosliceConeExtension

/-!
概要：cocartesian な後半の辺を持つ三角形の錐の延長。
方針：後半の辺の錐を延長し、二辺を内ホーン上で貼り、内 anodyne な join を充填する。
規約：最初の辺は δ₂、後半の辺は δ₀、長辺は δ₁。
使われ方：Kerodon Corollary 5.1.2.4（Tag 01TS）、Proposition 5.2.5.1（Tag 01VU） の transport の合成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：後半の辺が cocartesian な三角形の錐を最初の辺の錐から延長する。
方針：後半の辺の始点への相対制限で錐を延長し、内ホーンとの join を充填する。
規約：指定された部分パラメーターの錐と底の錐を厳密に保つ。
使われ方：Kerodon Corollary 5.1.2.4（Tag 01TS）、三角形から最初の辺への相対制限。 -/
lemma cocartesianTriangle_extendCone {X Y A : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (A₀ : A.Subcomplex) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ⟶ X)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) A ⟶ X) (B : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) A ⟶ Y)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ G = t)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ H = stdSimplex.δ (2 : Fin 3) ≫ t)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ B = t ≫ q)
    (hGH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ H)
    (hGq : G ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ B)
    (hHq : H ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ B) :
    ∃ T : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) A ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ T = t ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ T = G ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ T = H ∧ T ≫ q = B := by
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (0 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  let G₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G
  let H₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ H
  let B₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 A) ≫ B
  have hG₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ G₁ = stdSimplex.δ (0 : Fin 3) ≫ t := by
    dsimp only [G₁]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hG]
  have hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ H₁ =
      stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ t) := by
    dsimp only [H₁]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hH]
    rw [← Category.assoc, ← hv, Category.assoc]
  have hB₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ B₁ = (stdSimplex.δ (0 : Fin 3) ≫ t) ≫ q := by
    dsimp only [B₁]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hB, Category.assoc]
  have hGH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (A₀ : SSet.{u})) ≫ G₁ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ H₁ := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2))
      (𝟙 (A₀ : SSet.{u})) ≫ z) hGH
    simpa only [G₁, H₁, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
      Category.id_comp, hv] using h
  have hGq₁ : G₁ ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ B₁ := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 3))
      (𝟙 (A₀ : SSet.{u})) ≫ z) hGq
    simpa only [G₁, B₁, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
      Category.id_comp] using h
  have hHq₁ : H₁ ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A) ≫ B₁ := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ z) hHq
    simpa only [H₁, B₁, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
      Category.id_comp, hv] using h
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_source_of_isCocartesianEdge
    (stdSimplex.δ (0 : Fin 3) ≫ t) q he
  obtain ⟨J, hJ, hJb, hJs, hJq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeCosliceRestriction_extendCone
    (stdSimplex.δ (0 : Fin 3) ≫ t) q (stdSimplex.δ (1 : Fin 2)) A₀
    G₁ H₁ B₁ hG₁ hH₁ hB₁ hGH₁ hGq₁ hHq₁
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeft_horn₂₁_isPushout A
  let W := hs.desc H J hJs.symm
  have hWb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (horn 2 1 : SSet.{u})) A₀.ι ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 1).ι (𝟙 (A₀ : SSet.{u})) ≫ G := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeft_horn₂₁_isPushout (A₀ : SSet.{u})).hom_ext
    · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inl_desc H J hJs.symm)
      have hh := h.trans hGH.symm
      simpa only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, Category.id_comp,
        horn.ι_ι] using hh
    · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inr_desc H J hJs.symm)
      have hh := h.trans hJb
      simpa only [G₁, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
        Category.id_comp, horn.ι_ι] using hh
  have hWq : W ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 1).ι (𝟙 A) ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc]
      simpa only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, horn.ι_ι] using hHq
    · rw [← Category.assoc, hs.inr_desc]
      simpa only [B₁, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
        horn.ι_ι] using hJq
  let hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout (horn 2 1) A₀
  let V := hu.desc W G hWb
  have hVq : V ≫ q = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 1) A₀).ι ≫ B := by
    apply hu.hom_ext
    · rw [← Category.assoc, hu.inl_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι]
      exact hWq
    · rw [← Category.assoc, hu.inr_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι]
      exact hGq
  have hinner := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn (1 : Fin 3) (by decide)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_rightAnodyne (horn 2 1) A₀ hinner q InnerFibration.mem
  let sq : CommSq V (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 1) A₀).ι q B := ⟨hVq⟩
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 1).ι (𝟙 A) ≫ sq.lift = W := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, Category.assoc, sq.fac_left]
    exact hu.inl_desc _ _ _
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[2] : SSet.{u})) A₀.ι ≫ sq.lift = G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, Category.assoc, sq.fac_left]
    exact hu.inr_desc _ _ _
  refine ⟨sq.lift, ?_, hright, ?_, sq.fac_right⟩
  · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at h
    exact h.trans hG
  · rw [← horn.ι_ι (i := (1 : Fin 3)) (j := (2 : Fin 3)) (hij := by decide)]
    rw [← Category.comp_id (𝟙 A),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp horn₂₁.ι₀₁ (horn 2 1).ι (𝟙 A) (𝟙 A), Category.assoc, hleft]
    exact hs.inl_desc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
