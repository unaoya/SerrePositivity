module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismInitialPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverFunctor

/-!
概要：写像円柱側の比較の立方体の前面の pushout。
方針：初期部分 Z(0) の二つの生成部分を境界の写像円柱へ貼り、写像円柱の普遍性を使う。
規約：構造射 f の終域は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(0) と Z(m) の比較による同値判定。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：境界の写像円柱から全体の写像円柱への標準射。
方針：境界 prism の包含と底の恒等射を pushout から貼る。
規約：始域と終域を通常の pushout として明示する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、比較の立方体の前面の包含。 -/
noncomputable def relativeJoinBoundaryCylinderMap {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ⟶
      pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[m] : SSet.{u})) f :=
  pushout.desc (((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ≫ pushout.inl _ _)
    (pushout.inr _ _) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, pushout.condition,
        ← Category.assoc])

/-- 概要：境界の写像円柱の包含は円柱部分で境界の直積の包含になる。
方針：pushout の左包含の計算則を使う。
規約：底は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱の境界の自然性。 -/
lemma relativeJoinBoundaryCylinderMap_inl {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ≫
        relativeJoinBoundaryCylinderMap f =
      ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) f :=
  pushout.inl_desc _ _ _

/-- 概要：境界の写像円柱の包含は共通の終域を保つ。
方針：pushout の右包含の計算則を使う。
規約：終域は Y。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、写像円柱の境界の終域部分。 -/
lemma relativeJoinBoundaryCylinderMap_inr {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ≫
        relativeJoinBoundaryCylinderMap f = pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) f :=
  pushout.inr_desc _ _ _

/-- 概要：prism の初期部分を境界の写像円柱へ写す標準射。
方針：境界 prism は円柱部分、終端は f と終域の包含の合成で写す。
規約：二つの部分を初期部分の pushout から貼り合わせる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、比較の立方体の前面の上側の射。 -/
noncomputable def relativeJoinPrismInitialCylinderMap {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m : SSet.{u}) ⟶
      pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout m).desc (pushout.inl _ _)
    (f ≫ pushout.inr _ _) (by rw [pushout.condition, Category.assoc])

/-- 概要：初期部分の円柱への射は境界 prism で左包含を回収する。
方針：初期部分の pushout の左包含の計算則を使う。
規約：終端の写像円柱の係数は境界の構造射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、前面の境界部分の可換性。 -/
lemma relativeJoinPrismInitialCylinderMap_boundary {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialBoundary m ≫ relativeJoinPrismInitialCylinderMap f =
      pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout m).inl_desc _ _ _

/-- 概要：初期部分の円柱への射は終端で f と右包含の合成になる。
方針：初期部分の pushout の右包含の計算則を使う。
規約：終端の係数は標準 m 単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、前面の終端部分の可換性。 -/
lemma relativeJoinPrismInitialCylinderMap_endpoint {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialEndpoint m ≫ relativeJoinPrismInitialCylinderMap f =
      f ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout m).inr_desc _ _ _

/-- 概要：写像円柱の境界の包含と Z(0) の包含は可換な正方形を作る。
方針：初期部分の二つの包含で、写像円柱の誘導射の計算則を使う。
規約：底 Y の成分は恒等射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、前面の pushout の可換条件。 -/
lemma relativeJoinPrismInitialCylinderMap_square {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialCylinderMap f ≫ relativeJoinBoundaryCylinderMap f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) f := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitial_isPushout m).hom_ext
  · rw [← Category.assoc, relativeJoinPrismInitialCylinderMap_boundary,
      relativeJoinBoundaryCylinderMap_inl, ← Category.assoc]
    rfl
  · rw [← Category.assoc, relativeJoinPrismInitialCylinderMap_endpoint,
      Category.assoc, relativeJoinBoundaryCylinderMap_inr, ← Category.assoc]
    exact (pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) (g := f)).symm

/-- 概要：境界の写像円柱と prism は Z(0) に沿って全体の写像円柱を作る。
方針：初期部分の二つの成分上の可換性を、全体の写像円柱の普遍性へ移す。
規約：構造射 f と終域 Y は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、比較の立方体の前面の pushout。 -/
lemma relativeJoinCylinder_front_isPushout {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    IsPushout (relativeJoinPrismInitialCylinderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι
      (relativeJoinBoundaryCylinderMap f)
      (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m]) f) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary m : SSet.{u})
  let g := (boundary m).ι ≫ f
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialBoundary.{u} m ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι =
      ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) := rfl
  have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialEndpoint.{u} m ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[m] : SSet.{u}) := rfl
  apply IsPushout.mk' (relativeJoinPrismInitialCylinderMap_square f)
  · intro T w w' h₁ h₂
    apply pushout.hom_ext h₂
    have he := congrArg (fun k : pushout e g ⟶ T ↦ pushout.inr e g ≫ k) h₁
    dsimp only [e, g] at he
    simpa only [← Category.assoc, relativeJoinBoundaryCylinderMap_inr] using he
  · intro T a b h
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m] ≫ b = f ≫ (pushout.inr e g ≫ a) := by
      have he := congrArg (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m : SSet.{u}) ⟶ T ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialEndpoint m ≫ k) h
      have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialEndpoint m ≫
          (relativeJoinPrismInitialCylinderMap f ≫ a) = f ≫ (pushout.inr e g ≫ a) := by
        rw [← Category.assoc, relativeJoinPrismInitialCylinderMap_endpoint, Category.assoc]
      have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialEndpoint m ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι ≫ b) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[m] ≫ b := by
        rw [← Category.assoc, hE]
      exact hR.symm.trans (he.symm.trans hL)
    refine ⟨pushout.desc b (pushout.inr e g ≫ a) he, ?_, pushout.inl_desc _ _ _⟩
    apply pushout.hom_ext
    · rw [← Category.assoc, relativeJoinBoundaryCylinderMap_inl, Category.assoc, pushout.inl_desc]
      have he := congrArg (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m : SSet.{u}) ⟶ T ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialBoundary m ≫ k) h
      have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialBoundary m ≫
          (relativeJoinPrismInitialCylinderMap f ≫ a) = pushout.inl e g ≫ a := by
        rw [← Category.assoc, relativeJoinPrismInitialCylinderMap_boundary]
      have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeJoinPrismInitialBoundary m ≫
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismInitial m).ι ≫ b) = ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ≫ b := by
        rw [← Category.assoc, hB]
      exact hR.symm.trans (he.symm.trans hL)
    · rw [← Category.assoc, relativeJoinBoundaryCylinderMap_inr, pushout.inr_desc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
