module
public import SerrePositivity.KST.SConstruction.TracedSequenceBoundaryData
public import SerrePositivity.KST.SConstruction.PrescribedFamilyChainLifting

/-! # 先に指定した境界補正列を全区間で保持する列の族の厳密化
概要：先に構成した境界の補正列と全 trace を保持し、全パラメータの厳密な raw 写像族を作る。
方針：各段の元の適合区間と前段の全補正を、境界の指定全区間付きで持ち上げる。
規約：境界円柱の定数性を要求せず、実際の指定境界と射影区間を保持する。
使われ方：元の K prism の全精密化族を、先に指定した BF 境界へ厳密に制限する。
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
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n))
  (B : TracedSequenceBoundaryData X Y j f H)

/-- 全パラメータの補正済み段と、元の補正列・指定境界・境界の全区間。 -/
structure PrescribedSequenceFamilyStage (n : ℕ) where
  /-- 全パラメータの補正済み段。 -/
  val : U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right
  /-- 元の段の族からの全補正区間。 -/
  chain : FamilyHomotopyChain (f n) val
  /-- 先に指定した境界の同じ段への厳密な制限。 -/
  boundary : j ≫ val = (B.stage n).val
  /-- 境界の全区間は先に指定した同じ補正列の trace。 -/
  boundary_trace : (familyHomotopyChainTrace chain).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) =
    familyHomotopyChainTrace (B.stage n).chain

/-- 元の射影区間と指定境界の全区間を同時に保持して、次段を構成する。 -/
def prescribedSequenceFamilyNext (n : ℕ) (s : PrescribedSequenceFamilyStage X Y j f H B n) :
    {t : PrescribedSequenceFamilyStage X Y j f H B (n + 1) //
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
  have ht : (familyHomotopyChainTrace (B.stage (n + 1)).chain).map (· ≫ p) =
      (familyHomotopyChainTrace c).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
    rw [B.trace n]
    dsimp only [c]
    rw [familyHomotopyChainAppend_trace, familyHomotopyChainSingle_trace,
      familyHomotopyChainMap_trace]
    simp only [List.cons_append, List.nil_append, List.map_cons]
    rw [← s.boundary_trace]
    simp only [List.map_map, Function.comp_def, Category.assoc]
  let L := prescribedFamilyChainLiftData p j c (f (n + 1)) rfl (B.stage (n + 1)).chain ht
  exact ⟨⟨L.1, L.2.val, L.2.property.2.1, L.2.property.2.2.2⟩,
    L.2.property.1, L.2.property.2.2.1⟩

/-- 元の零段を保ち、指定境界の全区間を保持した段を順に構成する。 -/
def prescribedSequenceFamilyStage : (n : ℕ) → PrescribedSequenceFamilyStage X Y j f H B n
  | 0 => ⟨f 0, .nil (f 0), B.zero.symm, B.zero_trace.symm⟩
  | n + 1 => (prescribedSequenceFamilyNext X Y j f H B n (prescribedSequenceFamilyStage n)).val

/-- 指定境界の同じ全補正区間を保つ、構造射と厳密可換な全 raw 写像族。 -/
def prescribedSequenceFamilyRectification : U ⟶ RawSpectrumMapping.space X Y :=
  RawSpectrumMapping.lift X Y (fun n => (prescribedSequenceFamilyStage X Y j f H B n).val)
    (fun n => (prescribedSequenceFamilyNext X Y j f H B n
      (prescribedSequenceFamilyStage X Y j f H B n)).property.1)

/-- 各段の実評価は、指定境界を保って選んだ補正済み族そのもの。 -/
lemma prescribedSequenceFamilyRectification_evaluation (n : ℕ) :
    prescribedSequenceFamilyRectification X Y j f H B ≫ RawSpectrumMapping.evaluation X Y n =
      (prescribedSequenceFamilyStage X Y j f H B n).val :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ n

/-- 全 raw 写像族の境界は、先に構成した同じ境界 raw 写像族そのもの。 -/
lemma prescribedSequenceFamilyRectification_boundary :
    j ≫ prescribedSequenceFamilyRectification X Y j f H B =
      tracedSequenceBoundaryMap X Y j f H B := by
  apply RawSpectrumMapping.hom_ext X Y
  intro n
  rw [Category.assoc, prescribedSequenceFamilyRectification_evaluation,
    tracedSequenceBoundaryMap_evaluation]
  exact (prescribedSequenceFamilyStage X Y j f H B n).boundary

/-- 保存した全補正区間は、境界で指定した元の全補正区間を厳密に回収する。 -/
lemma prescribedSequenceFamilyStage_boundary_trace (n : ℕ) :
    (familyHomotopyChainTrace (prescribedSequenceFamilyStage X Y j f H B n).chain).map
      ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) = familyHomotopyChainTrace (B.stage n).chain :=
  (prescribedSequenceFamilyStage X Y j f H B n).boundary_trace

/-- 全段の射影 trace は元の適合区間と前段の全補正の像そのもの。 -/
lemma prescribedSequenceFamilyStage_trace (n : ℕ) :
    (familyHomotopyChainTrace (prescribedSequenceFamilyStage X Y j f H B (n + 1)).chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
      (H n).h :: (familyHomotopyChainTrace (prescribedSequenceFamilyStage X Y j f H B n).chain).map
        (· ≫ RawSpectrumMapping.step X Y n) := by
  change (familyHomotopyChainTrace
    (prescribedSequenceFamilyNext X Y j f H B n
      (prescribedSequenceFamilyStage X Y j f H B n)).val.chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) = _
  have h := (prescribedSequenceFamilyNext X Y j f H B n
    (prescribedSequenceFamilyStage X Y j f H B n)).property.2
  simpa only [familyHomotopyChainAppend_trace, familyHomotopyChainSingle_trace,
    familyHomotopyChainMap_trace, List.cons_append, List.nil_append] using h

/-- 零段の族は元のまま保持する。 -/
lemma prescribedSequenceFamilyRectification_zero :
    prescribedSequenceFamilyRectification X Y j f H B ≫ RawSpectrumMapping.evaluation X Y 0 =
      f 0 :=
  prescribedSequenceFamilyRectification_evaluation X Y j f H B 0

end SerrePositivity.KST.SConstruction
