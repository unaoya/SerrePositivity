module
public import SerrePositivity.KST.SConstruction.FamilyChainLifting
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # 元の全適合区間を trace に保持する列の族の厳密化
概要：元の各適合円柱と前段の補正全区間を保存し、構造射と厳密可換な列の族を構成する。
方針：元の適合区間を前段の補正の像へ連結し、全区間を順に写像空間の fibration へ持ち上げる。
規約：境界や成分の等式を追加入力せず、元の実区間とその射影を保持する。
使われ方：一点上の元の境界補正列を先に構成し、指定境界を保つ全族の厳密化へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open Spectra SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {U : SSet.{u}}
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)

/-- 元の段の族から補正済みの段へ向かう、全実区間を保持した状態。 -/
structure TracedSequenceFamilyStage (n : ℕ) where
  /-- 補正済みの同じ全パラメータの段。 -/
  val : U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right
  /-- 元の族からの全補正区間。 -/
  chain : FamilyHomotopyChain (f n) val

variable (H : ∀ n, SSet.Homotopy
  (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
  (f n ≫ RawSpectrumMapping.step X Y n))

/-- 元の適合区間と前段の補正を全て用い、次段を同じ射影 trace と共に構成する。 -/
def tracedSequenceFamilyNext (n : ℕ) (s : TracedSequenceFamilyStage X Y f n) :
    {t : TracedSequenceFamilyStage X Y f (n + 1) //
      t.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        s.val ≫ RawSpectrumMapping.step X Y n ∧
      (familyHomotopyChainTrace t.chain).map
        (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
        familyHomotopyChainTrace (familyHomotopyChainAppend (familyHomotopyChainSingle (H n))
          (familyHomotopyChainMap s.chain (RawSpectrumMapping.step X Y n)))} := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space
  let : Fibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration (X.sigma n) (Y.level (n + 1)).space
  let c := familyHomotopyChainAppend (familyHomotopyChainSingle (H n))
    (familyHomotopyChainMap s.chain (RawSpectrumMapping.step X Y n))
  let L := familyHomotopyChainLiftData p c (f (n + 1)) rfl
  exact ⟨⟨L.1, L.2.val⟩, L.2.property.1, L.2.property.2⟩

/-- 零段を保持し、全段を元の全補正区間と共に順に構成する。 -/
def tracedSequenceFamilyStage : (n : ℕ) → TracedSequenceFamilyStage X Y f n
  | 0 => ⟨f 0, .nil (f 0)⟩
  | n + 1 => (tracedSequenceFamilyNext X Y f H n (tracedSequenceFamilyStage n)).val

/-- 選んだ全段の射影 trace は、元の適合区間と前段の全補正の像そのもの。 -/
lemma tracedSequenceFamilyStage_trace (n : ℕ) :
    (familyHomotopyChainTrace (tracedSequenceFamilyStage X Y f H (n + 1)).chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
      (H n).h :: (familyHomotopyChainTrace (tracedSequenceFamilyStage X Y f H n).chain).map
        (· ≫ RawSpectrumMapping.step X Y n) := by
  change (familyHomotopyChainTrace
    (tracedSequenceFamilyNext X Y f H n (tracedSequenceFamilyStage X Y f H n)).val.chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) = _
  have h := (tracedSequenceFamilyNext X Y f H n (tracedSequenceFamilyStage X Y f H n)).property.2
  simpa only [familyHomotopyChainAppend_trace, familyHomotopyChainSingle_trace,
    familyHomotopyChainMap_trace, List.cons_append, List.nil_append] using h

/-- 全補正区間を保持した、構造射と厳密に可換な raw 写像族。 -/
def tracedSequenceFamilyRectification : U ⟶ RawSpectrumMapping.space X Y :=
  RawSpectrumMapping.lift X Y (fun n => (tracedSequenceFamilyStage X Y f H n).val)
    (fun n => (tracedSequenceFamilyNext X Y f H n (tracedSequenceFamilyStage X Y f H n)).property.1)

/-- 各段の評価は、同じ逐次構成で選んだ補正済み族そのもの。 -/
lemma tracedSequenceFamilyRectification_evaluation (n : ℕ) :
    tracedSequenceFamilyRectification X Y f H ≫ RawSpectrumMapping.evaluation X Y n =
      (tracedSequenceFamilyStage X Y f H n).val :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ n

/-- 厳密化後の各段は、保存した元の全区間によって元の段の族に結ばれる。 -/
lemma tracedSequenceFamilyRectification_chain (n : ℕ) :
    Nonempty (FamilyHomotopyChain (f n)
      (tracedSequenceFamilyRectification X Y f H ≫ RawSpectrumMapping.evaluation X Y n)) := by
  rw [tracedSequenceFamilyRectification_evaluation]
  exact ⟨(tracedSequenceFamilyStage X Y f H n).chain⟩

/-- 零段は元の族を変更しない。 -/
lemma tracedSequenceFamilyRectification_zero :
    tracedSequenceFamilyRectification X Y f H ≫ RawSpectrumMapping.evaluation X Y 0 = f 0 :=
  tracedSequenceFamilyRectification_evaluation X Y f H 0

end SerrePositivity.KST.SConstruction
