module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaYonedaFiniteCoproducts
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Core.LimitDiagramIso

/-!
概要：元の底の有限余積と、その P_Σ Yoneda 像の余積の存在。
方針：反対圏の有限積を元の全余錐へ戻し、構成済みの保存定理を適用する。
規約：元の底の有限積仮定をそのまま公開入力に保つ。
使われ方：表現可能前層の小余積を有限部分集合の filtered 余極限で構成する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の反対圏の有限積から元の底の全有限余積が存在する。
方針：離散形状の反転同型と同じ図式の双対極限を使う。
規約：空添字を含む元の有限図式を保持する。
使われ方：P_Σ Yoneda の有限余積表示の存在入力。 -/
lemma hasFiniteCoproducts_of_op_finiteProducts {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {J : Type u} [Finite J] (p : nerve (Discrete J) ⟶ C) : HasColimit p := by
  apply (F1B.kanHasColimit_iff_hasLimit_op p).mpr
  let e := discreteNerveOppositeIso J
  exact (hasLimit_iff_restrict_of_precompositionEquivalence (SSet.opFunctor.map p) e.inv
    (isPrecompositionEquivalence_of_iso e.symm)).mpr (hC J (e.inv ≫ SSet.opFunctor.map p))

/-- 概要：元の底の有限余積図式の Yoneda 像は P_Σ 内で同じ余積を持つ。
方針：元の指定余錐の存在と有限余積保存を合わせる。
規約：空添字と全ての元の脚を保持する。
使われ方：表現可能前層の小余積の有限段。 -/
lemma sigmaYoneda_finiteDiagram_hasColimit {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {J : Type u} [Finite J] (p : nerve (Discrete J) ⟶ C) :
    HasColimit ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) := by
  obtain ⟨c, hc⟩ := hasFiniteCoproducts_of_op_finiteProducts hC p
  exact ⟨mapJoinCocone (sigmaYonedaInfinityMap C) (JoinCocone.ulift.{u, u + 1} c),
    sigmaYoneda_finiteCoproduct_isColimit c hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
