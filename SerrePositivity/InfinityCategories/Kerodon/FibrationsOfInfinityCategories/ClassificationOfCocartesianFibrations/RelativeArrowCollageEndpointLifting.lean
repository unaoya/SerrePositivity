module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCollageMixedLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalInnerFibration

/-!
概要：区間実現の定値時間の左ホーンと区間を渡る一次元の持ち上げ。
方針：端点の pullback により元の射影へ戻し始域の輸送 prism を使う。
規約：二次元以上の混合ホーンは別の補題で扱う。
使われ方：区間実現の left fibration 性の残りの分岐。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：端点の逆像が left fibration なら時間一定の左ホーンは持ち上がる。
方針：底の射を端点を経由して表示し pullback の普遍性で充填を移す。
規約：両端に同じ補題を使う。
使われ方：区間実現の純粋な始域側と終域側の分岐。 -/
lemma leftHorn_hasLift_of_endpoint_pullback {E R B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (r : R ⟶ (Δ[1] : SSet.{u}) ⊗ B)
    (e : E ⟶ R) (k : Fin 2) (hp : IsPullback e p r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k B))
    (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (a : (horn (n + 1) i : SSet.{u}) ⟶ R) (b : (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ B)
    (sq : CommSq a (horn (n + 1) i).ι r b)
    (ht : b ≫ fst Δ[1] B = SSet.const (stdSimplex.obj₀Equiv.symm k)) : sq.HasLift := by
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prism_eq_comp_endpoint_of_fst k b ht
  have h : a ≫ r = ((horn (n + 1) i).ι ≫ (b ≫ snd Δ[1] B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k B := by
    rw [Category.assoc, hb]
    exact sq.w
  let a0 := hp.lift a ((horn (n + 1) i).ι ≫ (b ≫ snd Δ[1] B)) h
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
  have sq0 : CommSq a0 (horn (n + 1) i).ι p (b ≫ snd Δ[1] B) :=
    ⟨hp.lift_snd _ _ h⟩
  refine CommSq.HasLift.mk' { l := sq0.lift ≫ e, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, sq0.fac_left]
    exact hp.lift_fst _ _ h
  · rw [Category.assoc, hp.w, ← Category.assoc, sq0.fac_right]
    exact hb

/-- 概要：先頭の一次ホーンの標準包含は区間の零頂点に定値。
方針：唯一の面の頂点で射を検査する。
規約：任意の宇宙の標準区間を使う。
使われ方：区間を渡る辺の始点を元の始域へ戻す。 -/
lemma relativeArrowCollage_firstHorn_const :
    (horn 1 (0 : Fin 2)).ι =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
        (horn 1 (0 : Fin 2) : SSet.{u}) ⟶ Δ[1]) := by
  apply horn.hom_ext
  intro j hj
  fin_cases j
  · exact False.elim (hj rfl)
  · decide +revert

/-- 概要：底の区間を恒等辺として渡る一次ホーンは始域の輸送で持ち上がる。
方針：始点を pullback で始域へ戻し left fibration の充填を標準 prism に入れる。
規約：元の始域の射影の left fibration 性を使う。
使われ方：区間実現の零番目の一次ホーンの混合分岐。 -/
lemma relativeArrowCollage_crossing_edge_hasLift {E F B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (a : (horn 1 (0 : Fin 2) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 F))
    (b : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ B)
    (sq : CommSq a (horn 1 (0 : Fin 2)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q) b)
    (ht : b ≫ fst Δ[1] B = 𝟙 Δ[1]) : sq.HasLift := by
  let hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollage_inl_isPullback p q f hf
  have h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q =
      ((horn 1 (0 : Fin 2)).ι ≫ (b ≫ snd Δ[1] B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B := by
    rw [sq.w]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, ht, Category.comp_id, relativeArrowCollage_firstHorn_const]
      change SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ((horn 1 (0 : Fin 2)).ι ≫ (b ≫ snd Δ[1] B)) ≫
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : B ⟶ Δ[1])
      rw [SSet.comp_const]
    · rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.comp_id]
  let a0 := hp.lift a ((horn 1 (0 : Fin 2)).ι ≫ (b ≫ snd Δ[1] B)) h
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin 2) (by decide))
  have sq0 : CommSq a0 (horn 1 (0 : Fin 2)).ι p (b ≫ snd Δ[1] B) :=
    ⟨hp.lift_snd _ _ h⟩
  let l := lift (b ≫ fst Δ[1] B) sq0.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · change ((horn 1 (0 : Fin 2)).ι ≫ lift (b ≫ fst Δ[1] B) sq0.lift) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f = a
    have he : (horn 1 (0 : Fin 2)).ι ≫ lift (b ≫ fst Δ[1] B) sq0.lift =
        a0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, ht, Category.comp_id,
          relativeArrowCollage_firstHorn_const]
        change SSet.const _ = a0 ≫ SSet.const _
        rw [SSet.comp_const]
      · rw [Category.assoc, lift_snd, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.comp_id]
        exact sq0.fac_left
    rw [he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero]
    exact hp.lift_fst _ _ h
  · change (lift (b ≫ fst Δ[1] B) sq0.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q = b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_prism p q f hf]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact sq0.fac_right

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
