module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension

/-!
概要：錐の頂点を固定した図式のホモトピーの持ち上げ。
方針：点の coslice の left fibration に図式のホモトピーを持ち上げ、join と直積の比較で錐の族へ戻す。
規約：指定した錐の頂点は区間上で厳密に定値。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW） の錐の制限の cocartesian な辺の存在。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：図式のホモトピーは与えた錐から錐の頂点を固定して持ち上がる。
方針：点の coslice の left fibration の先頭端点の持ち上げを使い、join の右側の直積の比較で族にする。
規約：X は quasicategory、K は任意、初期錐と右因子上の族を厳密に固定する。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW） の cocartesian な錐の輸送。 -/
lemma coneHomotopy_extend {K X : SSet.{u}} [Quasicategory X]
    (F₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ X)
    (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (h₀ : SSet.ι₀ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F₀) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⊗ Δ[1] ⟶ X,
      SSet.ι₀ ≫ G = F₀ ∧ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ▷ Δ[1]) ≫ G = H ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ▷ Δ[1]) ≫ G = fst Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ F₀ := by
  let point := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ≫ F₀
  let s₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F₀ (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ F₀ = point from rfl)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection point
  let B := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H
  have hs₀ : s₀ ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection _ _
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_point_whiskerRight K q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))
  have hw : CommSq (snd (horn 1 0 : SSet.{u}) K ≫ s₀) ((horn 1 0).ι ▷ K) q B := by
    constructor
    rw [Category.assoc, hs₀]
    dsimp [B]
    rw [← Category.assoc ((horn 1 0).ι ▷ K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization,
      Category.assoc, Category.assoc]
    change snd (horn 1 0 : SSet.{u}) K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F₀) =
      snd (horn 1 0 : SSet.{u}) K ≫ (SSet.ι₀ ≫ H)
    rw [h₀]
  let L := hw.lift
  have hL₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = s₀ := by
    have hh := congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection K ≫ t) hw.fac_left
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using hh
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = s₀ := by
    dsimp [R]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding K, Category.assoc, ← Category.assoc
      (β_ (Δ[1] : SSet.{u}) K).hom, SymmetricCategory.symmetry, Category.id_comp]
    exact hL₀
  have hRq : R ≫ q = H := by
    dsimp [R, L]
    rw [Category.assoc, hw.fac_right]
    dsimp [B]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight (Δ[0] : SSet.{u}) K Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R
  refine ⟨G, ?_, ?_, ?_⟩
  · dsimp [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.joinTensorRight_ι₀, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, hR₀,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
  · dsimp [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
    exact hRq
  · dsimp [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight_inl, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
