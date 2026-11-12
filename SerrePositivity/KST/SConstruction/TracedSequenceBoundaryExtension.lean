module
public import SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyRectification

/-! # 補正済みの部分族を次の指定境界として保持する
概要：一段前に構成した部分族の全補正区間を、より大きいパラメータの指定境界にする。
方針：保存済みの段・補正列・射影 trace を次の境界データへそのまま渡す。
規約：境界の補正を選び直さず、各実区間と零段を保持する。
使われ方：合成列の共通面に沿う、入れ子の相対厳密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
  {T U V : SSet.{u}} (j : T ⟶ U) [Mono j] (k : U ⟶ V)
  (f : ∀ n, V ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n))
  (B : TracedSequenceBoundaryData X Y j (fun n => k ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y k f H))

/-- 先に補正済みの部分族の全段・全区間を、次の延長の境界として保存する。 -/
def extendedTracedSequenceBoundaryData : TracedSequenceBoundaryData X Y k f H where
  stage n :=
    let s := prescribedSequenceFamilyStage X Y j (fun n => k ≫ f n)
      (tracedSequenceBoundaryCompatibility X Y k f H) B n
    ⟨s.val, s.chain⟩
  zero := rfl
  zero_trace := rfl
  comm n := (prescribedSequenceFamilyNext X Y j (fun n => k ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y k f H) B n
      (prescribedSequenceFamilyStage X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility X Y k f H) B n)).property.1
  trace n := prescribedSequenceFamilyStage_trace X Y j (fun n => k ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y k f H) B n

/-- 次の境界 raw 族は、先に構成した部分族と同じ実写像である。 -/
lemma extendedTracedSequenceBoundaryData_map :
    tracedSequenceBoundaryMap X Y k f H (extendedTracedSequenceBoundaryData X Y j k f H B) =
      prescribedSequenceFamilyRectification X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility X Y k f H) B := by
  apply RawSpectrumMapping.hom_ext X Y
  intro n
  rw [tracedSequenceBoundaryMap_evaluation, prescribedSequenceFamilyRectification_evaluation]
  rfl

/-- 二回目の厳密化は、一回目の部分族そのものへ厳密に制限する。 -/
lemma prescribedSequenceFamilyRectification_extension [Mono k] :
    k ≫ prescribedSequenceFamilyRectification X Y k f H
      (extendedTracedSequenceBoundaryData X Y j k f H B) =
      prescribedSequenceFamilyRectification X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility X Y k f H) B := by
  rw [prescribedSequenceFamilyRectification_boundary, extendedTracedSequenceBoundaryData_map]

/-- 二回目の補正列は部分族上で一回目の全補正区間を厳密に回収する。 -/
lemma prescribedSequenceFamilyStage_extension_trace [Mono k] (n : ℕ) :
    (familyHomotopyChainTrace (prescribedSequenceFamilyStage X Y k f H
      (extendedTracedSequenceBoundaryData X Y j k f H B) n).chain).map
        ((k ▷ (Δ[1] : SSet.{u})) ≫ ·) =
      familyHomotopyChainTrace (prescribedSequenceFamilyStage X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility X Y k f H) B n).chain :=
  prescribedSequenceFamilyStage_boundary_trace X Y k f H
    (extendedTracedSequenceBoundaryData X Y j k f H B) n

end SerrePositivity.KST.SConstruction
