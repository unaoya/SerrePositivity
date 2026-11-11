module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TriangleConeGluing
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TriangleJoinLifting

/-!
概要：最初の辺と長辺が cocartesian な三角形の余錐を真ん中の頂点から延長する。
方針：最初の辺、長辺、外側ホーンと境界の join の順に相対的な余錐を充填する。
規約：境界上の余錐と底の余錐を同時に固定する。
使われ方：三角形の後半の辺の cocartesian 性の消去による判定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：最初と長い辺が cocartesian な三角形の余錐は真ん中の頂点から相対的に延長できる。
方針：終点から最初の辺の余錐を作り、長辺の普遍性で最初のホーンへ貼って充填する。
規約：パラメータは標準単体、その境界のデータを厳密に固定する。
使われ方：cocartesian 性の三角形に沿う消去。 -/
lemma cocartesianTriangle_extendConeFromMiddle {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))) (n : ℕ)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) (boundary n : SSet.{u}) ⟶ X)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[n] ⟶ X) (B : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) Δ[n] ⟶ Y)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ G = t)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ H = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫ t)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ B = t ≫ q)
    (hGH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
        (𝟙 (boundary n : SSet.{u})) ≫ G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (boundary n).ι ≫ H)
    (hGq : G ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (boundary n).ι ≫ B)
    (hHq : H ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
        (𝟙 _) ≫ B) :
    ∃ T : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[2] : SSet.{u}) Δ[n] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ T = t ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (boundary n).ι ≫ T = G ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) (𝟙 _) ≫ T = H ∧
      T ≫ q = B := by
  let A := (Δ[n] : SSet.{u})
  let A₀ := boundary.{u} n
  let Gf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G
  let Bf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ B
  have hGf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ Gf = stdSimplex.δ (2 : Fin 3) ≫ t := by
    dsimp only [Gf]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hG]
  have hBf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ Bf = (stdSimplex.δ (2 : Fin 3) ≫ t) ≫ q := by
    dsimp only [Bf]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hB, Category.assoc]
  have hGHf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (A₀ : SSet.{u})) ≫ Gf =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ H := by
    simpa only [A, A₀, Gf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id] using hGH
  have hGfq : Gf ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ Bf := by
    simpa only [A, A₀, Gf, Bf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
      Category.id_comp] using congrArg
        (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ z) hGq
  have hHqf : H ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ Bf := by
    simpa only [A, A₀, Bf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id] using hHq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_target (stdSimplex.δ (2 : Fin 3) ≫ t) q
  obtain ⟨Jf, hJf, hJfb, hJfs, hJfq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeCosliceRestriction_extendCone
    (stdSimplex.δ (2 : Fin 3) ≫ t) q (stdSimplex.δ (0 : Fin 2)) A₀
    Gf H Bf hGf hH hBf hGHf hGfq hHqf
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  let H₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A) ≫ Jf
  let Gh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G
  let Bh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 A) ≫ B
  have hGh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ Gh = stdSimplex.δ (1 : Fin 3) ≫ t := by
    dsimp only [Gh]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hG]
  have hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ H₀ = stdSimplex.δ (1 : Fin 2) ≫
      (stdSimplex.δ (1 : Fin 3) ≫ t) := by
    dsimp only [H₀]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hJf,
      ← Category.assoc, ← hv, Category.assoc]
  have hBh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ Bh = (stdSimplex.δ (1 : Fin 3) ≫ t) ≫ q := by
    dsimp only [Bh]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hB, Category.assoc]
  have hGHh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (A₀ : SSet.{u})) ≫ Gh =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ H₀ := by
    have h := congrArg
      (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (A₀ : SSet.{u})) ≫ z) hJfb
    simpa only [A, A₀, Gh, Gf, H₀, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
      Category.comp_id, hv] using h.symm
  have hGhq : Gh ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) A₀.ι ≫ Bh := by
    simpa only [A, A₀, Gh, Bh, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
      Category.id_comp] using congrArg
        (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ z) hGq
  have hH₀q : H₀ ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A) ≫ Bh := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A) ≫ z) hJfq
    simpa only [A, A₀, H₀, Bh, Bf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, hv] using h
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction_source_of_isCocartesianEdge
    (stdSimplex.δ (1 : Fin 3) ≫ t) q hh
  obtain ⟨Jh, hJh, hJhb, hJhs, hJhq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeCosliceRestriction_extendCone
    (stdSimplex.δ (1 : Fin 3) ≫ t) q (stdSimplex.δ (1 : Fin 2)) A₀
    Gh H₀ Bh hGh hH₀ hBh hGHh hGhq hH₀q
  let hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.joinLeft_horn₂₀_isPushout A
  let W := hs.desc Jf Jh hJhs.symm
  have hWb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (horn 2 0 : SSet.{u})) A₀.ι ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 0).ι (𝟙 (A₀ : SSet.{u})) ≫ G := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.joinLeft_horn₂₀_isPushout (A₀ : SSet.{u})).hom_ext
    · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inl_desc Jf Jh hJhs.symm)
      simpa only [A, A₀, Gf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
        Category.comp_id, horn.ι_ι] using h.trans hJfb
    · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[1] : SSet.{u})) A₀.ι ≫ z)
        (hs.inr_desc Jf Jh hJhs.symm)
      simpa only [A, A₀, Gh, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
        Category.comp_id, horn.ι_ι] using h.trans hJhb
  have hWq : W ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 0).ι (𝟙 A) ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc]
      simpa only [A, A₀, Bf, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
        Category.comp_id, horn.ι_ι] using hJfq
    · rw [← Category.assoc, hs.inr_desc]
      simpa only [A, A₀, Bh, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
        Category.comp_id, horn.ι_ι] using hJhq
  let hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout (horn 2 0) A₀
  let V := hu.desc W G hWb
  have hVq : V ≫ q = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn 2 0) A₀).ι ≫ B := by
    apply hu.hom_ext
    · rw [← Category.assoc, hu.inl_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι]
      exact hWq
    · rw [← Category.assoc, hu.inr_desc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι]
      exact hGq
  have hVc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv
      ((stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (horn 2 0) A₀ ≫ V)) := by
    rw [hu.inr_desc, hG]
    exact hf
  obtain ⟨L, hL, hLq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.triangleJoin_exists_lift q n V B hVq hVc
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (horn 2 0).ι (𝟙 A) ≫ L = W := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft_ι, Category.assoc, hL]
    exact hu.inl_desc _ _ _
  have hright : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[2] : SSet.{u})) A₀.ι ≫ L = G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι, Category.assoc, hL]
    exact hu.inr_desc _ _ _
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ L = Jf := by
    rw [← horn.ι_ι (i := (0 : Fin 3)) (j := (2 : Fin 3)) (hij := by decide)]
    rw [← Category.comp_id (𝟙 A),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp horn₂₀.ι₀₁ (horn 2 0).ι (𝟙 A) (𝟙 A), Category.assoc, hleft]
    exact hs.inl_desc _ _ _
  refine ⟨L, ?_, hright, ?_, hLq⟩
  · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] at h
    exact h.trans hG
  · have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A) ≫ z) hfirst
    simpa only [A, A₀, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id] using h.trans hJfs

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
