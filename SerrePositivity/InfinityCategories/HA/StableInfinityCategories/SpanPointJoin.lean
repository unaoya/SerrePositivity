module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.RightJoinCoproduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! # 標準 span と一点・離散二点の join

概要：標準 span Λ[2,0] は一点と二つの点の直和との join と同型である。
方針：二つの区間の始点に沿う pushout を標準ホーンの pushout と比較する。
規約：第一の枝の終点は第一の点、第二の枝の終点は第二の点。
使われ方：零始点を忘れて二項余積の余錐を取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二つの点の join の左端で二本を貼ると標準 span になる。
方針：標準ホーンの pushout を区間の join 表示へ移す。
規約：二つの区間の向きは共通始点から外向き。使われ方：標準形の同型の構成。 -/
lemma spanPointJoin_isPushout :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂) := by
  apply horn₂₀.isPushout.of_iso' (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0) (Iso.refl _)
  · simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
  · simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
  · simp
  · simp

/-- 概要：一点と離散二点の join は標準 span と同型である。
方針：共通左因子での右直和の pushout と、標準 span の pushout の普遍性を比較する。
規約：右因子は標準零単体二つの直和。使われ方：零始点を除く余錐の比較。 -/
def spanPointJoinIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≅ (horn 2 0 : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout Δ[0] Δ[0] Δ[0]).isoIsPushout _ _ spanPointJoin_isPushout

/-- 概要：第一の点と始点の区間は span の第一枝へ写る。
方針：pushout 比較同型の第一包含の式。
規約：標準区間の join 表示を使う。使われ方：第一の脚の照合。 -/
lemma spanPointJoinIso_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      spanPointJoinIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout Δ[0] Δ[0] Δ[0]).inl_isoIsPushout_hom _ _ _

/-- 概要：第二の点と始点の区間は span の第二枝へ写る。
方針：pushout 比較同型の第二包含の式。
規約：標準区間の join 表示を使う。使われ方：第二の脚の照合。 -/
lemma spanPointJoinIso_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      spanPointJoinIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout Δ[0] Δ[0] Δ[0]).inr_isoIsPushout_hom _ _ _

/-- 概要：左の一点は span の共通始点に写る。
方針：第一の区間を通して左包含を計算する。
規約：共通始点は第一枝の δ₁。使われ方：始対象条件の照合。 -/
lemma spanPointJoinIso_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ spanPointJoinIso.hom =
      stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ := by
  have h := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ f) spanPointJoinIso_left
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl] at h
  exact h

/-- 概要：右の第一の点は span の第一枝の終点に写る。
方針：右包含と第一の区間の比較を使う。
規約：終点は δ₀。使われ方：二点図式の第一対象の固定。 -/
lemma spanPointJoinIso_first :
    (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ spanPointJoinIso.hom =
        stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₁ := by
  have h := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ f) spanPointJoinIso_left
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr] at h
  exact h

/-- 概要：右の第二の点は span の第二枝の終点に写る。
方針：右包含と第二の区間の比較を使う。
規約：終点は δ₀。使われ方：二点図式の第二対象の固定。 -/
lemma spanPointJoinIso_second :
    (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ spanPointJoinIso.hom =
        stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂ := by
  have h := congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ f) spanPointJoinIso_right
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
