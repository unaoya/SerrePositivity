module
public import SerrePositivity.KST.SConstruction.TracedSequenceFamilyRectification

/-! # 元の適合区間から先に構成する指定境界の補正列
概要：境界上で元の全適合区間から補正列を先に構成し、全段の厳密可換式と trace を保存する。
方針：元の適合族を境界へ制限し、同じ全区間を保持した逐次厳密化を行う。
規約：境界の補正列の存在を追加入力せず、元の実区間から実構成する。
使われ方：一点上で先に選んだ BF 境界を保つ全精密化族の段の厳密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {T U : SSet.{u}} (j : T ⟶ U)
  (f : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step X Y n))

/-- 元の適合区間を、同じ境界パラメータの段の二合成へ制限する。 -/
def tracedSequenceBoundaryCompatibility (n : ℕ) :
    SSet.Homotopy
      ((j ≫ f (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space)
      ((j ≫ f n) ≫ RawSpectrumMapping.step X Y n) := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (H n) j
  exact
    { h := V.h
      h₀ := V.h₀.trans (Category.assoc _ _ _).symm
      h₁ := V.h₁.trans (Category.assoc _ _ _).symm
      rel := V.rel }

/-- 指定境界で全段の元の補正列と厳密可換式を保持する実データ。 -/
structure TracedSequenceBoundaryData where
  /-- 境界の各段と、元の段の制限からの全補正区間。 -/
  stage : ∀ n, TracedSequenceFamilyStage X Y (fun n => j ≫ f n) n
  /-- 境界の零段は元の族を変更しない。 -/
  zero : (stage 0).val = j ≫ f 0
  /-- 零段の補正区間は空である。 -/
  zero_trace : familyHomotopyChainTrace (stage 0).chain = []
  /-- 境界の段は構造射と厳密可換。 -/
  comm : ∀ n, (stage (n + 1)).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
    (stage n).val ≫ RawSpectrumMapping.step X Y n
  /-- 各段の全射影区間は元の適合区間と前段の全補正の像そのもの。 -/
  trace : ∀ n, (familyHomotopyChainTrace (stage (n + 1)).chain).map
    (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space) =
    ((j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h) ::
      (familyHomotopyChainTrace (stage n).chain).map (· ≫ RawSpectrumMapping.step X Y n)

/-- 元の適合族の境界制限から、同じ全区間を持つ境界補正列を実構成する。 -/
def canonicalTracedSequenceBoundaryData : TracedSequenceBoundaryData X Y j f H where
  stage := tracedSequenceFamilyStage X Y (fun n => j ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y j f H)
  zero := rfl
  zero_trace := rfl
  comm n := (tracedSequenceFamilyNext X Y (fun n => j ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y j f H) n
      (tracedSequenceFamilyStage X Y (fun n => j ≫ f n)
        (tracedSequenceBoundaryCompatibility X Y j f H) n)).property.1
  trace n := tracedSequenceFamilyStage_trace X Y (fun n => j ≫ f n)
    (tracedSequenceBoundaryCompatibility X Y j f H) n

/-- 境界補正列から得る、構造射と厳密に可換な元の境界 raw 写像族。 -/
def tracedSequenceBoundaryMap (B : TracedSequenceBoundaryData X Y j f H) :
    T ⟶ RawSpectrumMapping.space X Y :=
  RawSpectrumMapping.lift X Y (fun n => (B.stage n).val) B.comm

/-- 元の境界 raw 写像の各段は、保存した補正列の終点そのもの。 -/
lemma tracedSequenceBoundaryMap_evaluation (B : TracedSequenceBoundaryData X Y j f H) (n : ℕ) :
    tracedSequenceBoundaryMap X Y j f H B ≫ RawSpectrumMapping.evaluation X Y n =
      (B.stage n).val :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ n

end SerrePositivity.KST.SConstruction
