module


public meta import SerrePositivity.Util.Citation
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

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.1.2.17" (partial := component) "仮定：余デカルト・ファイブレーション p と底への写像 q（Lean は任意の q を許し、HA では h₁ のファイバーの包含）。結論：底変換が余デカルト・ファイブレーションになる部分に一致する。色別の圏の族を分類する関手 χ と operad 上への延長は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd
attribute [cite HA "4.1.1.14" (partial := direction) "仮定：単体集合上の余デカルトファイブレーションと底変換写像（HA の p が対称モノイダルである方向の余デカルト性に一致）。結論：引き戻し写像は余デカルトファイブレーションとなる（Assoc⊗ への底変換に適用した片方向に一致）。逆向きの二単体による検出は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd
attribute [cite HA "4.1.3.11" (partial := direction) "仮定：底変換の単体写像（Lean では planar 条件は不要。HA の Cut を底変換に取る）。結論：元の射影が余デカルトなら引き戻しも余デカルトで、元で余デカルトな辺の引き戻しも余デカルトとなる（この二つの含意に一致）。planar 条件と逆向きの検出は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd
attribute [cite HA "4.1.3.11" (partial := direction) "仮定：底変換の単体写像（Lean では planar 条件は不要。HA の Cut を底変換に取る）。結論：元の射影が余デカルトなら引き戻しも余デカルトで、元で余デカルトな辺の引き戻しも余デカルトとなる（この二つの含意に一致）。planar 条件と逆向きの検出は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_pullback
attribute [cite HA "4.2.1.20" (partial := component) "仮定：余デカルトファイブレーションと底変換写像（Lean では Assoc⊗→LM⊗ を明示する）。結論：引き戻した写像は余デカルトファイブレーションとなる（代数色への制限の余デカルト性に一致）。Assoc 上の operadic 構造は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd
attribute [cite HA "4.3.1.18" (partial := component) "仮定：余デカルトファイブレーションとその底変換（Lean では BM⊗ への各包含を明示する）。結論：制限した射影が余デカルトになる（左右のテンソル構造を作る射影の成分に一致）。二つの作用が可換となる整合性は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_pullback_snd
attribute [cite HTT "2.4.1.11" (partial := stronger-hyp) "仮定：p-inner fibration の辺 e に大域的 IsCartesianEdge p e を追加（Lean が強い）。結論：isCartesianEdge_pullback を p(e):Δ1→S への引戻しと diagonal lift e に適用すると、同じ引戻し X×SΔ1 の同じ辺が Cartesian。局所 Cartesian の表示条件はこの追加仮定の下で得るが、元の大域性なしの局所述語を束ねた定義はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback
attribute [cite HTT "2.4.1.3" (partial := component) "仮定：任意の Cartesian edge の pullback（HTT の (2) と一致）。結論：isCartesianEdge_pullback はその同じ辺の Cartesian 性を保つので (2) に一致。また comp と、全対象が準圏という追加仮定下の cancellation は (3) の両方向を与える。(1) の全 iso と一般の simplicial sets での cancellation は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback
attribute [cite HTT "2.4.2.10" (partial := direction) "仮定：p が CartesianFibration（原典 iff の順方向と一致）。結論：任意 Δn→S の pullback は Cartesian なので、とくに n≤2 の条件に一致。逆方向はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd
attribute [cite HTT "2.4.2.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd
attribute [cite HTT "2.4.2.6" (partial := stronger-hyp) "仮定：p が大域的 CartesianFibration と追加（Lean が強い）。結論：cartesianFibration_pullback_snd を任意の辺 Δ1→S に適用し、その同じ pullback の Cartesian 性を得るので原典の local-Cartesian の条件はこの場合に成り立つ。一般の local lifting と二条件の iff を束ねる型はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_pullback_snd
