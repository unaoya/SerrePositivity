module

public import SerrePositivity.KST.Spectra.ShiftedKanSequence
public import SerrePositivity.KST.Spectra.SignedAdjointComposition
public import SerrePositivity.KST.Spectra.TwistedKanSequence
public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.KST.Spectra.KanLoopLift
public import SerrePositivity.KST.Spectra.PointedCurryingComponents

/-!
概要：元の Ω 列の随伴構造射から符号を変えた loop 列へのホモトピー可換な比較。
方針：随伴構造射を Kan 円へ持ち上げ、二回合成の符号の式を各段に適用する。
規約：構造可換式は点つき射の成分の等式。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の元の対象からの実際の射の構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 円の loop 列の構造射の符号を変え、一段をずらした列。
方針：円の次数 -1 の前合成で構造射を変更して零段を落とす。
規約：まだ構造射を単射へ置換しない。
使われ方：BF 1978 §2。元の列の随伴構造射をホモトピー可換にする標的。 -/
def signedLoopTail (X : KanSequence.{u}) : KanSequence.{u} :=
  tail (twist (mappingPre (CirclePower.integerPowerMap.{u} (-1)) X))

/-- 概要：符号を変えて一段をずらした loop 列も Ω 条件を満たす。
方針：内部 Hom の Ω 条件、符号反転の同型性、添字移動を合成する。
規約：全基点・零次数を含む Ω 条件。
使われ方：BF 1978 §2、HA §1.4.2。符号を変えた列の BF 置換への入力。 -/
theorem signedLoopTail_omegaCondition {X : KanSequence.{u}} (hX : X.OmegaCondition) :
    (signedLoopTail X).OmegaCondition :=
  tail_omegaCondition (twist_omegaCondition
    (mappingPre (CirclePower.integerPowerMap.{u} (-1)) X)
    (mapping_omegaCondition CirclePower.space.{u} X hX)
    (fun n => LoopMappingClasses.pre_neg_one_piIsomorphism (X.level n).space))

/-- 概要：Kan 列の随伴構造射を Kan 円の loop へ持ち上げる。
方針：通常の円から Kan 円への源の制限の RLP を使う。
規約：各段の実際の点つき射。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号を変えた loop 列への比較の成分。 -/
def kanAdjoint (X : KanSequence.{u}) (n : ℕ) :
    (X.level n).space ⟶ PointedObject.basedHom CirclePower.space.{u} (X.level (n + 1)).space :=
  kanLoopLift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n))

/-- 概要：持ち上げた随伴構造射は通常の円への制限で元の随伴構造射へ戻る。
方針：Kan loop への持ち上げの比較式を使う。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2。二回の随伴構造射の合成の書き換え。 -/
@[reassoc]
theorem kanAdjoint_comparison (X : KanSequence.{u}) (n : ℕ) :
    kanAdjoint X n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n) :=
  kanLoopLift_comparison _

/-- 概要：Ω 条件の列の持ち上げた随伴構造射は全基点 π_* 同型。
方針：通常の随伴の同型性を Kan 円へ持ち上げる。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7。厳密化する比較の各段の同型性。 -/
theorem kanAdjoint_piIsomorphism {X : KanSequence.{u}} (hX : X.OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAdjoint X n).right :=
  kanLoopLift_piIsomorphism _ (hX n)

/-- 概要：符号を変えた loop 列の随伴構造射の明示式。
方針：内部 Hom の随伴構造射の交換の式の後に符号反転を合成する。
規約：元の列の一段先の構造射を用いる。
使われ方：BF 1978 §2。持ち上げた随伴構造射の構造可換式の検査。 -/
theorem signedLoopTail_adjoint (X : KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((signedLoopTail X).sigma n) =
      (ihom CirclePower.space.{u}).map
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 1))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} PointedSimplicialSet.circle.{u}
        (X.level (n + 2)).space).hom ≫
      (ihom PointedSimplicialSet.circle.{u}).map
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1))
          (X.level (n + 2)).space) := by
  change MonoidalClosed.curry ((mapping CirclePower.space.{u} X).sigma (n + 1) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1))
      (X.level (n + 2)).space) = _
  rw [MonoidalClosed.curry_natural_right]
  have h := mapping_adjoint CirclePower.space.{u} X (n + 1)
  change MonoidalClosed.curry ((mapping CirclePower.space.{u} X).sigma (n + 1)) = _ at h
  rw [h, Category.assoc]

/-- 概要：持ち上げた随伴構造射は符号を変えた loop 列へ成分で構造可換となる。
方針：随伴を取り、二回合成の符号の式を適用して uncurry で戻す。
規約：単射構造射による厳密化の前の主張。
使われ方：Goerss–Jardine I §7、BF 1978 §2。元のスペクトルからの実際の有理化写像の比較の入力。 -/
theorem kanAdjoint_signedLoopTail_comm {X : KanSequence.{u}} (hX : X.OmegaCondition) (n : ℕ) :
    PointedMapping.componentOf (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫
      (signedLoopTail X).sigma n) =
      PointedMapping.componentOf (X.sigma n ≫ kanAdjoint X (n + 1)) := by
  apply PointedMapping.componentOf_of_curry
  change PointedMapping.componentOf (MonoidalClosed.curry
      (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫ (signedLoopTail X).sigma n)) =
    PointedMapping.componentOf (MonoidalClosed.curry (X.sigma n ≫ kanAdjoint X (n + 1)))
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_right]
  change PointedMapping.componentOf (kanAdjoint X n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((signedLoopTail X).sigma n)) =
    PointedMapping.componentOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n) ≫
      (ihom PointedSimplicialSet.circle.{u}).map (kanAdjoint X (n + 1)))
  erw [signedLoopTail_adjoint X n, ← kanAdjoint_comparison X n,
    ← kanAdjoint_comparison X (n + 1)]
  exact signed_adjoint_composition (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2)))
    (hX (n + 2)) (kanAdjoint X n) (kanAdjoint X (n + 1))

end

end SerrePositivity.KST.Spectra.KanSequence
