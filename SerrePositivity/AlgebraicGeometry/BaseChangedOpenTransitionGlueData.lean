module

public import SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
public import SerrePositivity.AlgebraicGeometry.OpenTransitionGlueData

/-!
概要：後段での六種の実際の式を、具体的な Scheme.GlueData へ組み立てる。
方針：対角の二側の逆から IsIso を得て、既存の gluing 構成へ渡す。
規約：六種の式の供給は別の一致判定の適用。ここは gluing の係数移送の法則。
使われ方：G2 の実際の有限表示対象の模型の貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {S B : Scheme.{u}} (C : OpenTransitionCandidate S) (γ : B ⟶ S)

/-- 後段の実際の対角・反転・三重交叉に対する六種の式。 -/
structure BaseChangedEquations : Prop where
  diagonalRight : ∀ i, C.baseChangedD γ i ≫ C.baseChangedF γ i i = 𝟙 _
  diagonalLeft : ∀ i, C.baseChangedF γ i i ≫ C.baseChangedD γ i = 𝟙 _
  reverseDiagonal : ∀ i, C.baseChangedT γ i i = 𝟙 _
  reverseInverse : ∀ i j, C.baseChangedT γ i j ≫ C.baseChangedT γ j i = 𝟙 _
  tripleFst : ∀ i j k, C.baseChangedL γ i j k ≫ C.baseChangedF γ j k =
    pullback.fst (C.baseChangedF γ i j) (C.baseChangedF γ i k) ≫
      C.baseChangedT γ i j ≫ C.baseChangedF γ j i
  tripleSnd : ∀ i j k, C.baseChangedL γ i j k ≫ C.baseChangedT γ j k ≫ C.baseChangedF γ k j =
    pullback.snd (C.baseChangedF γ i j) (C.baseChangedF γ i k) ≫
      C.baseChangedT γ i k ≫ C.baseChangedF γ k i

/-- 六種の実際の式から、後段の実際の gluing datum を構成する。 -/
def baseChangedOpenTransitionGlueData (h : C.BaseChangedEquations γ) : Scheme.GlueData.{u} := by
  letI (i : C.J) : IsIso (C.baseChangedF γ i i) :=
    ⟨⟨C.baseChangedD γ i, h.diagonalLeft i, h.diagonalRight i⟩⟩
  exact openTransitionGlueData (fun i ↦ pullback γ (C.p i))
    (fun ij ↦ pullback γ (C.q ij.1 ij.2)) (C.baseChangedF γ) (C.baseChangedT γ)
    (C.baseChangedL γ) h.tripleFst h.reverseDiagonal h.reverseInverse h.tripleSnd

end SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
