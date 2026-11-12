module
public import SerrePositivity.KST.SConstruction.TerminalPathSuffix

/-! # 元の区間族の suffix を終点固定 path にする
概要：終点が基点の区間族から、元の path から定数 path への具体的な族を構成する。
方針：max による再パラメータ付けの後で評価し、点つき curry で戻す。
規約：パラメータの Kan 性や基点は要求しない。使われ方：収縮からの fiber 内のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 元の区間族の suffix は全時刻で終点を基点へ送る。 -/
lemma terminalSuffixFamily_basepoint {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) :
    terminalPointedInterval.hom ▷ (A ⊗ (Δ[1] : SSet.{u})) ≫
      terminalSuffixReparametrization A ≫ h =
        toUnit ((𝟙_ SSet.{u}) ⊗ (A ⊗ (Δ[1] : SSet.{u}))) ≫ B.hom := by
  rw [← Category.assoc, terminalSuffixReparametrization_end]
  simp only [Category.assoc, h₁, comp_toUnit_assoc]

/-- 元の区間族から終点固定 path の suffix の族への射。 -/
def terminalSuffixFamily {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) :
    A ⊗ (Δ[1] : SSet.{u}) ⟶ (terminalPathSpace B).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry terminalPointedInterval B
    (terminalSuffixReparametrization A ≫ h) (terminalSuffixFamily_basepoint B h h₁)

/-- suffix の各始点は元の区間族を厳密に回収する。 -/
lemma terminalSuffixFamily_start {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁) :
    terminalSuffixFamily B h h₁ ≫ (terminalPathStart B).right = h := by
  rw [terminalPathStart_evaluation, ← Category.assoc, terminalSuffixFamily,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, Spectra.KanPath.evaluation,
    ← Category.assoc, curry_pre_app, Spectra.KanPath.curry_unit_evaluation]
  have he := congrArg (fun f => f ≫ h) (terminalSuffixReparametrization_start A)
  simpa only [Category.assoc, Category.id_comp] using he

/-- 時刻零の suffix の族は元の終点固定 path の族。 -/
lemma terminalSuffixFamily_zero {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁) :
    SSet.ι₀ ≫ terminalSuffixFamily B h h₁ = terminalPathFamily B h h₁ := by
  apply (cancel_mono (PointedObject.basedHomι terminalPointedInterval B)).mp
  have hs : terminalPointedInterval.right ◁ (SSet.ι₀ : A ⟶ _) ≫
      terminalSuffixReparametrization A = (β_ (Δ[1] : SSet.{u}) A).hom :=
    terminalSuffixReparametrization_zero A
  rw [Category.assoc, terminalSuffixFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← curry_natural_left, ← Category.assoc, hs,
    terminalPathFamily_ι]

/-- 時刻一の suffix の族は定数 path に厳密に一致する。 -/
lemma terminalSuffixFamily_one {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁) :
    SSet.ι₁ ≫ terminalSuffixFamily B h h₁ = toUnit A ≫ (terminalPathSpace B).hom := by
  apply (cancel_mono (PointedObject.basedHomι terminalPointedInterval B)).mp
  have hs : terminalPointedInterval.right ◁ (SSet.ι₁ : A ⟶ _) ≫
      terminalSuffixReparametrization A = snd (Δ[1] : SSet.{u}) A ≫ SSet.ι₁ :=
    terminalSuffixReparametrization_one A
  rw [Category.assoc, terminalSuffixFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι,
    ← curry_natural_left, ← Category.assoc, hs,
    Category.assoc, h₁, comp_toUnit_assoc, Category.assoc,
    PointedObject.basedHom_basepoint_ι, PointedObject.curry_constant]
  rfl

end SerrePositivity.KST.SConstruction
