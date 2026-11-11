module

public import SerrePositivity.KST.Spectra.GroupActionCochainAdjoint
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
概要：作用スペクトルの cochain の厳密な余単体 Kan Ω 列。
方針：随伴構造射を uncurry し、余単体の自然性から構造射との可換性を得る。
規約：構造射の単射性はまだ要求せず、BF 置換は各次数の対象について別に与える。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。hG の余単体模型のスペクトル構造。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：指定した cochain 次数の実際の Kan 列。
方針：各スペクトル段の cochain と uncurry した随伴構造射を束ねる。
規約：各段の Kan 性は自由軌道の内部 Hom 表示による。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain のスペクトル段の列。 -/
def sequence {G : Type u} [Group G] (A : GroupAction.{u} G) (j : SimplexCategory) :
    KanSequence.{u} where
  level n := {
    space := (GroupActionCochains.level A n).obj j
    kan := inferInstance }
  sigma n := MonoidalClosed.uncurry ((adjointTransformation A n).app j)

/-- 概要：cochain の Kan 列の随伴構造射は構成した余単体随伴射の成分。
方針：curry と uncurry の往復の公式を使う。
規約：厳密な点つき射の等式。
使われ方：HA §1.4.2。cochain の Ω 条件の照合。 -/
lemma sequence_adjoint {G : Type u} [Group G] (A : GroupAction.{u} G)
    (j : SimplexCategory) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((sequence A j).level n).space ((sequence A j).level (n + 1)).space
      ((sequence A j).sigma n) = (adjointTransformation A n).app j :=
  curry_uncurry _

/-- 概要：各 cochain 次数の Kan 列は Ω 条件を満たす。
方針：随伴構造射の全基点 π_* 同型を各成分へ適用する。
規約：厳密 Ω 同型の仮定は不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の安定ホモトピー群の入力。 -/
lemma sequence_omegaCondition {G : Type u} [Group G] (A : GroupAction.{u} G)
    (j : SimplexCategory) : (sequence A j).OmegaCondition := by
  intro n
  rw [sequence_adjoint]
  exact adjointTransformation_piIsomorphism A n j

/-- 概要：余単体の射は cochain の Kan 列の間の厳密な射を与える。
方針：余単体の随伴構造射の自然性を uncurry する。
規約：構造射との可換性は厳密な等式。
使われ方：Goerss–Jardine VIII §2。余単体 Kan Ω 列の構造射。 -/
def sequenceMap {G : Type u} [Group G] (A : GroupAction.{u} G)
    {i j : SimplexCategory} (f : i ⟶ j) : sequence A i ⟶ sequence A j where
  app n := (GroupActionCochains.level A n).map f
  comm n := by
    have hn := (adjointTransformation A n).naturality f
    change (GroupActionCochains.level A n).map f ≫ (adjointTransformation A n).app j =
      (adjointTransformation A n).app i ≫
        (ihom PointedSimplicialSet.circle.{u}).map
          ((GroupActionCochains.level A (n + 1)).map f) at hn
    have h := congrArg MonoidalClosed.uncurry hn
    rw [uncurry_natural_left, uncurry_natural_right] at h
    exact h

/-- 概要：群作用の cochain は Kan 列の圏の厳密な余単体図式。
方針：余単体の各段の射を構造可換射へ束ね、関手法則を段ごとに示す。
規約：この図式の各対象は Ω 条件を満たす。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。Tot を段ごとに取るための実際の図式。 -/
def diagram {G : Type u} [Group G] (A : GroupAction.{u} G) :
    CosimplicialObject KanSequence.{u} where
  obj := sequence A
  map := sequenceMap A
  map_id j := by
    apply KanSequence.Hom.ext_app
    intro n
    exact (GroupActionCochains.level A n).map_id j
  map_comp f g := by
    apply KanSequence.Hom.ext_app
    intro n
    exact (GroupActionCochains.level A n).map_comp f g

/-- 概要：各 cochain 次数の Kan Ω 列は実際の BF 対象へ置換できる。
方針：構成済みの単射構造射の置換を各対象に適用する。
規約：ここでは各次数の対象の置換であり、BF 置換の余単体関手性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。cochain の各次数の Sp の対象としての表示。 -/
def spectrum {G : Type u} [Group G] (A : GroupAction.{u} G) (j : SimplexCategory) :
    OmegaSpectrum.{u} :=
  (sequence A j).cofibrantOmegaSpectrum (sequence_omegaCondition A j)

end

end SerrePositivity.KST.Spectra.GroupActionCochains
