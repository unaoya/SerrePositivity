module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：指定した底の標準単体上の weighted nerve 図式を最後の係数値へ写す。
方針：標準単体と有限順序集合の nerve の同型で底変換し、最後の頂点の係数へ評価する。
規約：添字の有限順序集合は宇宙 u に持ち上げ、係数と同じ宇宙で weighted nerve を取る。
使われ方：Kerodon §5.3.3（Tag 025W）、相対左ホーンから最後の Kan 複体のホーンへの移送。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の射列を、持ち上げた有限順序集合からの通常の関手として表示する。
方針：ULift の順序同型で添字を戻して射列に続ける。
規約：添字の対象と射は係数の宇宙 u に置く。
使われ方：Kerodon §5.3.3（Tag 025W）、標準単体上の weighted nerve の底変換の関手。 -/
def weightedNerveSimplexIndexFunctor {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) : ULift.{u} (Fin (n + 1)) ⥤ C :=
  ULift.orderIso.monotone.functor ⋙ σ

/-- 概要：持ち上げた射列の nerve は元の底の標準単体の射を表す。
方針：各次数で標準単体の順序写像と持ち上げた射列の合成を計算する。
規約：標準単体から有限順序集合の nerve への同型を前合成する。
使われ方：Kerodon §5.3.3（Tag 025W）、相対的な図式の底変換の可換条件。 -/
lemma weightedNerveSimplexIndexFunctor_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    (stdSimplex.isoNerve.{u} n).hom ≫ nerveMap (weightedNerveSimplexIndexFunctor σ) =
      SSet.yonedaEquiv.symm σ := by
  apply SSet.hom_ext
  rintro ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：持ち上げた有限順序集合の最後の頂点は終対象。
方針：全ての頂点から最後への順序射と射の一意性を使う。
規約：n=0 も含む。
使われ方：Kerodon §5.3.3（Tag 025W）、標準単体の最後の係数値への評価。 -/
def weightedNerveSimplexIndexTerminal (n : ℕ) :
    IsTerminal (ULift.up (Fin.last n) : ULift.{u} (Fin (n + 1))) :=
  IsTerminal.ofUniqueHom (fun i ↦ homOfLE (Fin.le_last i.down))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：底の標準単体上の相対図式を最後の係数値へ写す。
方針：射列の添字の nerve 上に図式を引き戻し、その終対象で係数を評価する。
規約：パラメータ T は任意で、底の図式 b は厳密に固定する。
使われ方：Kerodon §5.3.3（Tag 025W）、相対ホーンを最後の係数のホーンへ移す構成。 -/
noncomputable def weightedNerveSimplexCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ) :
    T ⟶ F.obj (σ.obj (Fin.last n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift (weightedNerveSimplexIndexFunctor σ) F a
      (b ≫ (stdSimplex.isoNerve.{u} n).hom) (by
        rw [Category.assoc, weightedNerveSimplexIndexFunctor_projection]
        exact ha) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation (weightedNerveSimplexIndexFunctor σ ⋙ F)
      (weightedNerveSimplexIndexTerminal.{u} n)

/-- 概要：weighted nerve の相対ホーンから最後の係数値へのホーンを作る。
方針：ホーンの底の標準単体への包含を指定して相対図式の係数評価を使う。
規約：欠ける面 k に制限はなく、係数の Kan 性も構成には不要。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 充填に渡すホーンの実際の単体集合の射。 -/
noncomputable def weightedNerveHornLastCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    (horn (n + 1) k : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))) :=
  weightedNerveSimplexCoefficient F σ a (horn (n + 1) k).ι ha

/-- 概要：最後の係数値が Kan なら、相対ホーンの係数評価を充填できる。
方針：構成したホーンの射へ通常の Kan 充填を適用する。
規約：ここでは最後の単体を回収し、他の面との一致は別途図式の自然性で確認する。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の左ホーン充填の最後の係数の充填。 -/
lemma exists_weightedNerveHornLastCoefficient_filler {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))),
      (horn (n + 1) k).ι ≫ H = weightedNerveHornLastCoefficient F σ k a ha := by
  obtain ⟨H, hH⟩ := KanComplex.hornFilling (weightedNerveHornLastCoefficient F σ k a ha)
  exact ⟨H, hH.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
