module

public import SerrePositivity.KST.Spectra.PointedWeightedEndMap
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensor
public import SerrePositivity.KST.Spectra.FilteredKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceForgetful

/-!
概要：Kan Ω 列の図式の段ごとの homotopy end と BF 置換。
方針：各段で点つき Bousfield–Kan end を取り、随伴構造射の end と loop の交換で Ω 条件を移す。
規約：段の構造射の単射性は最後に置換で回復する。Sp の ∞ 極限性を主張しない。
使われ方：HA §1.4.2、BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）。hG・Tot の実際のスペクトルの対象。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KanSequence

variable {I : Type u} [SmallCategory I]

/-- 概要：段ごとの end の随伴構造射。
方針：元の随伴の自然変換を end に送り、loop と end の点つき交換同型の逆を合成する。
規約：構造射の単射性はまだ要求しない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の Ω 条件の計算。 -/
def homotopyLimitAdjoint (D : I ⥤ KanSequence.{u}) (n : ℕ) :
    PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D (n + 1))) :=
  PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (adjointTransformation D n) ≫
    (PointedWeightedEnd.cotensorIso PointedSimplicialSet.circle.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D (n + 1))).inv

/-- 概要：Kan 列の図式の各段で end を取った Kan 列。
方針：各段の Kan 性を end のホーン充填で示し、構造射は随伴射を uncurry する。
規約：cofibrant 置換前の実際の列。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の置換前の模型。 -/
def homotopyLimit (D : I ⥤ KanSequence.{u}) : KanSequence.{u} where
  level n := {
    space := PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)
    kan := inferInstance }
  sigma n := uncurry (homotopyLimitAdjoint D n)

/-- 概要：end の Kan 列の随伴構造射は指定した end の随伴射そのもの。
方針：curry と uncurry の逆関係を使う。
規約：点つき射の厳密な等式。
使われ方：HA §1.4.2。Ω 条件を全基点の π_* 同型へ還元する。 -/
theorem homotopyLimit_adjoint (D : I ⥤ KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((homotopyLimit D).level n).space
      ((homotopyLimit D).level (n + 1)).space ((homotopyLimit D).sigma n) =
        homotopyLimitAdjoint D n :=
  curry_uncurry _

/-- 概要：段ごとの Kan homotopy end は Ω 条件を保つ。
方針：係数の全基点 π_* 同型の保存と loop 交換の実際の同型を合成する。
規約：添字の有限性や図式の遷移の fibration 性を要求しない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の fibrant 条件。 -/
theorem homotopyLimit_omegaCondition (D : I ⥤ KanSequence.{u})
    (hD : ∀ i, (D.obj i).OmegaCondition) : (homotopyLimit D).OmegaCondition := by
  intro n
  let E := levelDiagram D (n + 1) ⋙ ihom PointedSimplicialSet.circle.{u}
  let : ∀ i, KanComplex (E.obj i).right :=
    fun i ↦ loopSpace_kanComplex ((D.obj i).level (n + 1)).space
  have hm : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (adjointTransformation D n)).right :=
    PointedWeightedEnd.map_piIsomorphism (adjointTransformation D n) (fun i ↦ hD i n)
  let e := PointedWeightedEnd.cotensorIso PointedSimplicialSet.circle.{u}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D (n + 1))
  let e' : (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) E).right ≅
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (levelDiagram D (n + 1)))).right := PointedSimplicialSet.forget.mapIso e.symm
  have hc := hm.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e')
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((homotopyLimit D).level n).space
    ((homotopyLimit D).level (n + 1)).space ((homotopyLimit D).sigma n)).right
  rw [homotopyLimit_adjoint]
  exact hc

/-- 概要：Kan Ω 列の homotopy end を BF 対象へ束ねる。
方針：証明した Ω 条件を渡し、cofibrant 置換で単射構造射を回復する。
規約：元の図式の構造射に単射性を要求しない。
使われ方：HA §1.4.2、BF 1978 §2。置換前の余単体 Kan 列からの Tot。 -/
def homotopyLimitSpectrum (D : I ⥤ KanSequence.{u}) (hD : ∀ i, (D.obj i).OmegaCondition) :
    OmegaSpectrum.{u} :=
  (homotopyLimit D).cofibrantOmegaSpectrum (homotopyLimit_omegaCondition D hD)

/-- 概要：BF 置換から元の段ごとの homotopy end への比較。
方針：Kan Ω 列の単射置換の標準射を使う。
規約：各段で全単射への RLP を持つ。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の π_* の検査を元の Kan end へ戻す。 -/
def homotopyLimitProjection (D : I ⥤ KanSequence.{u}) (hD : ∀ i, (D.obj i).OmegaCondition) :
    Hom (homotopyLimitSpectrum D hD).toKanSequence (homotopyLimit D) :=
  (homotopyLimit D).cofibrantOmegaProjection (homotopyLimit_omegaCondition D hD)

/-- 概要：BF homotopy end の比較射は各段で全基点 π_* 同型。
方針：単射置換の全単射 RLP による同型性を取り出す。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。hG・Tot の置換不変性。 -/
theorem homotopyLimitProjection_levelwise (D : I ⥤ KanSequence.{u})
    (hD : ∀ i, (D.obj i).OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyLimitProjection D hD).app n).right :=
  replacementProjection_piIsomorphism (homotopyLimit D) n

end KanSequence

namespace OmegaSpectrum

/-- 概要：BF 図式の段ごとの homotopy end を BF 対象へ束ねる。
方針：忘却後の Kan Ω 列の end を作り、構造射の単射性を cofibrant 置換で回復する。
規約：Sp の ∞ 極限の普遍性は含まない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の実際のスペクトルの対象。 -/
def homotopyLimit {I : Type u} [SmallCategory I] (D : I ⥤ OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (KanSequence.homotopyLimit (D ⋙ forgetToKan)).cofibrantOmegaSpectrum
    (KanSequence.homotopyLimit_omegaCondition (D ⋙ forgetToKan)
      (fun i ↦ (D.obj i).toKanSequence_omega))

end OmegaSpectrum

end

end SerrePositivity.KST.Spectra
