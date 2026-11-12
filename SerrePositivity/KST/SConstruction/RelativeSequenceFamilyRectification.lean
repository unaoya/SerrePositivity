module
public import SerrePositivity.KST.SConstruction.RelativeFamilyChains
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # 指定パラメータ境界を保つ列の写像族の厳密化
概要：元の各段の適合ホモトピーを用い、境界を固定したまま列の族を厳密可換にする。
方針：前段の補正を実ホモトピーの有限列で保持し、次段の制限 fibration に持ち上げる。
規約：元の族・指定境界を全段で保持する。境界固定の適合ホモトピーを入力とする。
使われ方：K の全入力データを BF の実写像空間に接続するパラメータ付き帰納構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open Spectra
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
  {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)

/-- 一段の族と、元の指定族から境界を固定して得た実ホモトピーの有限列。 -/
structure RelativeSequenceFamilyStage (n : ℕ) where
  /-- この段で補正した実際の全パラメータ族。 -/
  val : U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right
  /-- 元の族からの境界固定の補正を、実際の有限列として保存する。 -/
  chain : RelativeFamilyChain j (f n) val

variable (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n))
  (hrel : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h =
    fst T (Δ[1] : SSet.{u}) ≫ j ≫ f (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)

/-- 前段の補正を含む全ての元の区間を用いて、次段の族を境界固定で厳密化する。 -/
def relativeSequenceFamilyNext (n : ℕ) (s : RelativeSequenceFamilyStage X Y j f n) :
    {t : RelativeSequenceFamilyStage X Y j f (n + 1) //
      t.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        s.val ≫ RawSpectrumMapping.step X Y n ∧
      (relativeFamilyChainTrace t.chain).map
        (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
      relativeFamilyChainTrace (relativeFamilyChainAppend
        (relativeFamilyChainSingle j (H n) (hrel n))
        (relativeFamilyChainMap s.chain (RawSpectrumMapping.step X Y n)))} := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space
  let : Fibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration (X.sigma n) (Y.level (n + 1)).space
  let c := relativeFamilyChainAppend (relativeFamilyChainSingle j (H n) (hrel n))
    (relativeFamilyChainMap s.chain (RawSpectrumMapping.step X Y n))
  let hex := exists_relativeFamilyChain_lift_with_trace p j c (f (n + 1)) rfl
  exact ⟨⟨hex.choose, hex.choose_spec.2.choose⟩,
    hex.choose_spec.1, hex.choose_spec.2.choose_spec⟩

/-- 次段の全補正区間の射影は、元の適合区間と前段の指定補正の像を厳密に回収する。 -/
lemma relativeSequenceFamilyNext_trace (n : ℕ)
    (s : RelativeSequenceFamilyStage X Y j f n) :
    (relativeFamilyChainTrace (relativeSequenceFamilyNext X Y j f H hrel n s).val.chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
    relativeFamilyChainTrace (relativeFamilyChainAppend
      (relativeFamilyChainSingle j (H n) (hrel n))
      (relativeFamilyChainMap s.chain (RawSpectrumMapping.step X Y n))) :=
  (relativeSequenceFamilyNext X Y j f H hrel n s).property.2

/-- 零段から順に修正し、全パラメータ境界を元のまま保持する。 -/
def relativeSequenceFamilyStage : (n : ℕ) → RelativeSequenceFamilyStage X Y j f n
  | 0 => ⟨f 0, .nil (f 0)⟩
  | n + 1 => (relativeSequenceFamilyNext X Y j f H hrel n
      (relativeSequenceFamilyStage n)).val

/-- 全段で構造射と厳密可換な、元の族の境界固定補正。 -/
def relativeSequenceFamilyRectification : U ⟶ RawSpectrumMapping.space X Y :=
  RawSpectrumMapping.lift X Y
    (fun n => (relativeSequenceFamilyStage X Y j f H hrel n).val)
    (fun n => (relativeSequenceFamilyNext X Y j f H hrel n
      (relativeSequenceFamilyStage X Y j f H hrel n)).property.1)

/-- 実写像空間の各段の評価は、同じ逐次構成で選んだ族そのもの。 -/
lemma relativeSequenceFamilyRectification_evaluation (n : ℕ) :
    relativeSequenceFamilyRectification X Y j f H hrel ≫ RawSpectrumMapping.evaluation X Y n =
      (relativeSequenceFamilyStage X Y j f H hrel n).val :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ n

/-- 厳密化は全段で元の指定したパラメータ境界を厳密に保持する。 -/
lemma relativeSequenceFamilyRectification_boundary (n : ℕ) :
    j ≫ relativeSequenceFamilyRectification X Y j f H hrel ≫
      RawSpectrumMapping.evaluation X Y n = j ≫ f n := by
  rw [relativeSequenceFamilyRectification_evaluation]
  exact relativeFamilyChain_boundary (relativeSequenceFamilyStage X Y j f H hrel n).chain

/-- 各段の補正は、元の族から境界固定の実ホモトピーの有限列で結ばれる。 -/
lemma relativeSequenceFamilyRectification_chain (n : ℕ) :
    Nonempty (RelativeFamilyChain j (f n)
      (relativeSequenceFamilyRectification X Y j f H hrel ≫
        RawSpectrumMapping.evaluation X Y n)) := by
  rw [relativeSequenceFamilyRectification_evaluation]
  exact ⟨(relativeSequenceFamilyStage X Y j f H hrel n).chain⟩

/-- 零段は元の指定族を修正せず厳密に回収する。 -/
lemma relativeSequenceFamilyRectification_zero :
    relativeSequenceFamilyRectification X Y j f H hrel ≫
      RawSpectrumMapping.evaluation X Y 0 = f 0 :=
  relativeSequenceFamilyRectification_evaluation X Y j f H hrel 0

end SerrePositivity.KST.SConstruction
