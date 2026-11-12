module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：cartesian・cocartesian 辺の底変換。
方針：元の射で持ち上げた単体と新しい底の単体を引き戻しに組み合わせる。
規約：p の q に沿う底変換は pullback.snd p q とする。
使われ方：Kerodon §5.1.1（Tag 01T4）・§5.1.4（Tag 01U9）、fibration の底変換での閉性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：引き戻しの辺の第一射影が cartesian なら元の辺も cartesian。
方針：第一射影の持ち上げを引き戻しの普遍性で新しい底へ戻す。
規約：第二射影に関する cartesian 性を結論する。
使われ方：Kerodon §5.1.1（Tag 01T4）、cartesian fibration の底変換。 -/
lemma isCartesianEdge_pullback {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (e : (pullback p q) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p ((pullback.fst p q).app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (pullback.snd p q) e := by
  intro n a b ha sq
  have sq₁ : CommSq (a ≫ pullback.fst p q)
      (horn (n + 2) (Fin.last (n + 2))).ι p (b ≫ q) := by
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, sq.w, Category.assoc]
  have := he n (a ≫ pullback.fst p q) (b ≫ q)
    (by change (pullback.fst p q).app _ (a.app _ _) = _; rw [ha]) sq₁
  refine CommSq.HasLift.mk' {
    l := pullback.lift sq₁.lift b sq₁.fac_right
    fac_left := ?_
    fac_right := pullback.lift_snd _ _ _ }
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using sq₁.fac_left
  · simpa only [Category.assoc, pullback.lift_snd] using sq.w.symm

/-- 概要：引き戻しの辺の第一射影が cocartesian なら元の辺も cocartesian。
方針：第一射影の持ち上げと底の単体を引き戻しに組み合わせる。
規約：第二射影に関する cocartesian 性を結論する。
使われ方：Kerodon §5.1.1（Tag 01T4）、cocartesian fibration の底変換。 -/
lemma isCocartesianEdge_pullback {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (e : (pullback p q) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((pullback.fst p q).app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.snd p q) e := by
  intro n a b ha sq
  have sq₁ : CommSq (a ≫ pullback.fst p q) (horn (n + 2) 0).ι p (b ≫ q) := by
    constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, sq.w, Category.assoc]
  have := he n (a ≫ pullback.fst p q) (b ≫ q)
    (by change (pullback.fst p q).app _ (a.app _ _) = _; rw [ha]) sq₁
  refine CommSq.HasLift.mk' {
    l := pullback.lift sq₁.lift b sq₁.fac_right
    fac_left := ?_
    fac_right := pullback.lift_snd _ _ _ }
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using sq₁.fac_left
  · simpa only [Category.assoc, pullback.lift_snd] using sq.w.symm

/-- 概要：cartesian fibration は底変換で閉じる。
方針：元の辺の lift を新しい底の辺と引き戻しで組み合わせる。
規約：底変換の射は pullback.snd p q。
使われ方：Kerodon §5.1.4（Tag 01U9）、fiber ごとの fibration の構成。 -/
instance cartesianFibration_pullback_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd p q) where
  mem := by
    refine ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p)), ?_⟩
    intro x e he
    have hbase : stdSimplex.δ 0 ≫ (e ≫ q) =
        SSet.yonedaEquiv.symm ((pullback.fst p q).app (Opposite.op ⦋0⦌) x) ≫ p := by
      rw [← Category.assoc, he]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc, pullback.condition]
    obtain ⟨f, hf, hfp, hfc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := p) |>.2
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) x) (e ≫ q)
        (by simpa only [SSet.yonedaEquiv_symm_comp] using hbase)
    refine ⟨pullback.lift f e hfp, ?_, pullback.lift_snd _ _ _, ?_⟩
    · apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst, SSet.yonedaEquiv_symm_comp] using hf
      · simpa only [Category.assoc, pullback.lift_snd, SSet.yonedaEquiv_symm_comp] using he
    · apply isCartesianEdge_pullback
      rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
      exact hfc

/-- 概要：cocartesian fibration は底変換で閉じる。
方針：元の辺の lift を新しい底の辺と引き戻しで組み合わせる。
規約：底変換の射は pullback.snd p q。
使われ方：Kerodon §5.1.4（Tag 01U9）、fiber ごとの fibration の構成。 -/
instance cocartesianFibration_pullback_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd p q) where
  mem := by
    refine ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p)), ?_⟩
    intro x e he
    have hbase : stdSimplex.δ 1 ≫ (e ≫ q) =
        SSet.yonedaEquiv.symm ((pullback.fst p q).app (Opposite.op ⦋0⦌) x) ≫ p := by
      rw [← Category.assoc, he]
      simp only [← SSet.yonedaEquiv_symm_comp, Category.assoc, pullback.condition]
    obtain ⟨f, hf, hfp, hfc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.mem (p := p) |>.2
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) x) (e ≫ q)
        (by simpa only [SSet.yonedaEquiv_symm_comp] using hbase)
    refine ⟨pullback.lift f e hfp, ?_, pullback.lift_snd _ _ _, ?_⟩
    · apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst, SSet.yonedaEquiv_symm_comp] using hf
      · simpa only [Category.assoc, pullback.lift_snd, SSet.yonedaEquiv_symm_comp] using he
    · apply isCocartesianEdge_pullback
      rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
      exact hfc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
