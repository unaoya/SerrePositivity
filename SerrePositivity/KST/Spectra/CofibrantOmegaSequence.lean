module

public import SerrePositivity.KST.Spectra.CofibrantKanSequence
public import SerrePositivity.KST.Spectra.PostMappingLifts
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-!
概要：Kan 列の逐次的な単射置換による Ω 条件の保存。
方針：比較射を loop に移して π_* 同型を得て、随伴構造射の可換正方形で打ち消す。
規約：全ての基点・零次数を含む π_* 同型で検証する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。BF の cofibrant–fibrant 対象への置換。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：列の厳密な射は随伴構造射とも可換。
方針：suspension 構造射の可換式に随伴の Hom 同値を適用する。
規約：点つき内部 Hom の後合成で loop の射を表す。
使われ方：BF 1978 §2、HA §1.4.2。Ω 条件の移送。 -/
theorem Hom.adjoint_comm {X Y : KanSequence.{u}} (f : Hom X Y) (n : ℕ) :
    f.app n ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space) (Y.sigma n) =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n) ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1)) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  have h := congrArg (adj.homEquiv (X.level n).space (Y.level (n + 1)).space) (f.comm n)
  change (adj.homEquiv _ _)
    ((PointedObject.smashFunctor.obj PointedSimplicialSet.circle.{u}).map (f.app n) ≫ Y.sigma n) =
      (adj.homEquiv _ _) (X.sigma n ≫ f.app (n + 1)) at h
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at h
  exact h

/-- 概要：全ての単射への RLP を各段で持つ比較射は標的の Ω 条件を源へ移す。
方針：比較射とその loop は π_* 同型であり、可換正方形から前の射を打ち消す。
規約：Ω 条件の対象は構造射の随伴である。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。置換の fibrant 条件。 -/
theorem Hom.omegaCondition_of_target {X Y : KanSequence.{u}} (f : Hom X Y)
    (hf : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (f.app n).right)
    (hY : Y.OmegaCondition) : X.OmegaCondition := by
  intro n
  let a := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n)
  let b := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space) (Y.sigma n)
  let p := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1))
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight p.right
    (PointedMapping.post_rlp_monomorphisms _ _ (hf (n + 1)))
  have hn : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight (f.app n).right (hf n)
  have heq : a.right ≫ p.right = (f.app n).right ≫ b.right :=
    congrArg Under.Hom.right (f.adjoint_comm n).symm
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (a.right ≫ p.right) := by
    rw [heq]
    exact hn.comp (hY n)
  exact hc.of_comp hp

/-- 概要：逐次的な単射置換は Ω 条件を保つ。
方針：構成した比較射の各段の RLP に Ω 条件の移送を適用する。
規約：元の構造射の単射性は不要。
使われ方：BF 1978 §2、HTT A.3.3。任意の Kan Ω 列の cofibrant 置換。 -/
theorem cofibrantReplacement_omegaCondition (X : KanSequence.{u}) (hX : X.OmegaCondition) :
    X.cofibrantReplacement.OmegaCondition :=
  (replacementProjection X).omegaCondition_of_target
    (fun n ↦ (replacementStage X n).projection_rlp) hX

/-- 概要：構造射が単射とは限らない Kan Ω 列を本レーンの Ω スペクトルへ置換する。
方針：逐次置換の単射性と検証済みの Ω 条件を束ねる。
規約：各段の比較射は全基点 π_* 同型。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。Sp の対象としての置換出力。 -/
def cofibrantOmegaSpectrum (X : KanSequence.{u}) (hX : X.OmegaCondition) : OmegaSpectrum.{u} :=
  X.cofibrantReplacement.toOmegaSpectrum (fun _n ↦ inferInstance)
    (X.cofibrantReplacement_omegaCondition hX)

/-- 概要：Ω スペクトルへの束ね直し後も元の Kan 列への厳密な比較射を持つ。
方針：各段と構造射が同じであることを使う。
規約：この射は Ω 列を Sp の対象へ置換する比較である。
使われ方：BF 1978 §2、HTT A.3.3。置換前の構造射との接続。 -/
def cofibrantOmegaProjection (X : KanSequence.{u}) (hX : X.OmegaCondition) :
    Hom (X.cofibrantOmegaSpectrum hX).toKanSequence X := replacementProjection X

end

end SerrePositivity.KST.Spectra.KanSequence

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

/-- 概要：Ω スペクトルに逐次的な単射置換を適用した対象。
方針：Kan 列へ忘却して構成済みの Ω 条件を移す。
規約：元も BF 対象の場合の自己比較であり、一般の Ω 列にも同じ構成がある。
使われ方：BF 1978 §2、HTT A.3.3。置換のスペクトル上の π_* 比較。 -/
def cofibrantReplacement (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  X.toKanSequence.cofibrantOmegaSpectrum X.toKanSequence_omega

/-- 概要：置換した Ω スペクトルから元の対象への厳密な射。
方針：Kan 列の比較射の各段と可換条件を用いる。
規約：通常の Ω スペクトルの圏の射。
使われ方：BF 1978 §2、HA §1.4.2。置換の誘導準同型。 -/
def cofibrantProjection (X : OmegaSpectrum.{u}) : X.cofibrantReplacement ⟶ X where
  app := X.toKanSequence.replacementProjection.app
  comm := X.toKanSequence.replacementProjection.comm

/-- 概要：Ω スペクトルの逐次置換の比較射は全整数次数の π_* 同型。
方針：検証済みの各段の全基点 π_* 同型を整数次数に移す。
規約：coherent nerve 内の同値との比較は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 のための置換不変性。 -/
theorem cofibrantProjection_piIsomorphism (X : OmegaSpectrum.{u}) :
    PiIsomorphism X.cofibrantProjection :=
  piIsomorphism_of_levelwise _ (X.toKanSequence.replacementProjection_piIsomorphism)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
