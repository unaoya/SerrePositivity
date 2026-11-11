module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberCoordinates

/-!
概要：反転した表現可能な weighted nerve から coherent な錐の全空間への実際の射。
方針：組み立てた cone simplex を join の同型で左 coslice の simplex にする。
規約：底は元の nerve の ULift、始点は x の標準頂点で固定する。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4（Tag 03B5） の係数図式と coherent な錐の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：weighted nerve の simplex を始点 x の左 coslice の simplex にする。
方針：cone simplex を点と標準単体の join の同型で移す。
規約：元の simplex の係数は反転した sHom の図式に値を持つ。
使われ方：HTT 4.2.4.1 の実際の左 coslice 比較の各次数。 -/
noncomputable def weightedCosliceSimplex (F : I ⥤ C) (x : C) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))) _⦋n⦌ := by
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x s.2), ?_⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex_apex]

/-- 概要：左 coslice の simplex の構成は全ての面・退化と可換。
方針：join の標準同型の自然性と cone simplex の添字変換則を使う。
規約：元の単体圏の射は左 cone の初点を固定して拡張する。
使われ方：HTT 4.2.4.1 の比較射の単体的自然性。 -/
lemma weightedCosliceSimplex_naturality (F : I ⥤ C) (x : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))).map α.op
      (weightedCosliceSimplex F x s) =
    weightedCosliceSimplex F x
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)).map α.op s) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x s.2)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso m).hom ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap _ α s).2)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_point_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  exact congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex_reindex F x α s.2)

/-- 概要：左 coslice の比較 simplex の射影は元の図式の simplex。
方針：join の右包含が δ 0 に対応することと cone の底の式を使う。
規約：係数は射影では忘れる。
使われ方：HTT 4.2.4.1 の比較が底の図式を保つことの検証。 -/
lemma weightedCosliceSimplex_projection (F : I ⥤ C) (x : C) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))).app
      (Opposite.op ⦋n⦌) (weightedCosliceSimplex F x s) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app (Opposite.op ⦋n⦌) (ULift.up s.1) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x s.2))) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_leftPoint_inr,
    stdSimplex.δ_comp_yonedaEquiv_symm, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex_tail, Equiv.apply_symm_apply]

/-- 概要：反転した表現可能な weighted nerve から始点固定の左 coslice への実際の射。
方針：全次数の simplex の構成を面・退化の自然性でまとめる。
規約：始域は対象の宇宙に合わせて ULift する。
使われ方：HTT 4.2.4.1 の coherent な錐と豊穣 Hom の図式の比較。 -/
noncomputable def weightedCosliceComparison (F : I ⥤ C) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) where
  app _ := ↾fun s ↦ weightedCosliceSimplex F x s.down
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    exact (weightedCosliceSimplex_naturality F x α.unop s.down).symm

/-- 概要：左 coslice の比較射は底の図式への射影と厳密に可換。
方針：各次数で比較 simplex の射影の式を使う。
規約：底の nerve の宇宙の持ち上げを明示する。
使われ方：HTT 4.2.4.1 の coherent cone の引き戻しへの持ち上げ。 -/
lemma weightedCosliceComparison_over (F : I ⥤ C) (x : C) :
    weightedCosliceComparison F x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) =
    (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact weightedCosliceSimplex_projection F x s.down

/-- 概要：反転した豊穣係数の weighted nerve から coherent cone の全空間への底上の射。
方針：左 coslice の比較射と weighted nerve の射影を引き戻しへ持ち上げる。
規約：追加の Kan 性・極限性・選択した Hom の逆射を使わない。
使われ方：HTT 4.2.4.1 の係数図式全体の実際の比較射。 -/
noncomputable def weightedCoherentConeComparison (F : I ⥤ C) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeTotal (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) :=
  pullback.lift (weightedCosliceComparison F x)
    ((SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (weightedCosliceComparison_over F x)

/-- 概要：coherent cone の全空間への比較射は元の nerve の上の射。
方針：引き戻しへの持ち上げと第二射影の合成を計算する。
規約：始域の射影は weighted nerve の射影の ULift。
使われ方：HTT 4.2.4.1 の fiber と切断の比較に適用する底上の可換条件。 -/
lemma weightedCoherentConeComparison_over (F : I ⥤ C) (x : C) :
    weightedCoherentConeComparison F x ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) =
    (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
