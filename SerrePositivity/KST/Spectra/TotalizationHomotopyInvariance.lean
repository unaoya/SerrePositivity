module

public import SerrePositivity.KST.Spectra.TotalizationRelativeWhitehead
public import SerrePositivity.KST.Spectra.CosimplicialProjectionEquivalence

/-!
概要：Reedy Kan 図式の通常の Tot による各段の全基点 π_* 同型の保存。
方針：射を二つの Reedy fibration へ分解し、相対 Whitehead と厳密な切断の等式を使う。
規約：各段の始域の参照頂点を明示する。点つき版では基点を使う。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot の具体的なホモトピー不変性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Reedy Kan な図式の各段の全基点 π_* 同型は通常の Tot でも全基点 π_* 同型。
方針：二射影分解の Tot での相対 Whitehead と共通の切断を使う。
規約：元の射自体が Reedy fibration であることは要求しない。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot の係数の同型保存。 -/
lemma CosimplicialTotalization.map_piIsomorphism
    {X Y : CosimplicialObject SSet.{u}}
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    [KanComplex (CosimplicialTotalization.obj X)]
    [KanComplex (CosimplicialTotalization.obj Y)]
    (f : X ⟶ Y)
    (hX : reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from X))
    (hY : reedyRight simplex SSet.modelCategoryQuillen.J.rlp (terminal.from Y))
    (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j)) (e₀ : ∀ j, X.obj j _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (CosimplicialTotalization.map f) := by
  let : ∀ j, KanComplex ((CosimplicialTwoProjections.obj f).obj j) :=
    fun j ↦ CosimplicialTwoProjections.obj_kanComplex f hY j
  let : KanComplex (CosimplicialTotalization.obj (CosimplicialTwoProjections.obj f)) :=
    CosimplicialTotalization.kanComplex _
      ((CosimplicialHornFibration.terminal_iff _).mp
        (CosimplicialTwoProjections.obj_reedy f hX hY))
  let eu : ∀ j, (CosimplicialTwoProjections.obj f).obj j _⦋0⦌ :=
    fun j ↦ (CosimplicialTwoProjections.inclusion f).app j |>.app _ (e₀ j)
  have hr := CosimplicialTotalization.map_piIsomorphism_of_reedyFibration
    (CosimplicialTwoProjections.sourceProjection f)
    (CosimplicialTwoProjections.sourceProjection_reedy f hY)
    (CosimplicialTwoProjections.sourceProjection_levelwise f e₀) eu
  have hq := CosimplicialTotalization.map_piIsomorphism_of_reedyFibration
    (CosimplicialTwoProjections.targetProjection f)
    (CosimplicialTwoProjections.targetProjection_reedy f hX)
    (CosimplicialTwoProjections.targetProjection_levelwise f hf e₀) eu
  have hcomp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (CosimplicialTotalization.map (CosimplicialTwoProjections.inclusion f) ≫
        CosimplicialTotalization.map (CosimplicialTwoProjections.sourceProjection f)) := by
    rw [← CosimplicialTotalization.map_comp,
      CosimplicialTwoProjections.inclusion_sourceProjection, CosimplicialTotalization.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  have hi := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hr
  have h := hi.comp hq
  rw [← CosimplicialTotalization.map_comp,
    CosimplicialTwoProjections.inclusion_targetProjection] at h
  exact h

/-- 概要：Reedy Kan な点つき図式の各段の π_* 同型は通常の点つき Tot でも同型。
方針：各基点を参照頂点として基礎図式の Tot のホモトピー不変性へ渡す。
規約：相対 matching の Reedy 条件を両図式の終射に課す。
使われ方：Goerss–Jardine VIII §1。点つき Tot の置換比較。 -/
lemma PointedTotalization.map_piIsomorphism
    {X Y : CosimplicialObject PointedSimplicialSet.{u}}
    [∀ j, KanComplex (X.obj j).right] [∀ j, KanComplex (Y.obj j).right]
    [KanComplex (PointedTotalization.obj X).right]
    [KanComplex (PointedTotalization.obj Y).right]
    (f : X ⟶ Y)
    (hX : reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget)))
    (hY : reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (terminal.from (Y ⋙ PointedSimplicialSet.forget)))
    (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedTotalization.map f).right := by
  let : ∀ j, KanComplex ((X ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (X.obj j).right)
  let : ∀ j, KanComplex ((Y ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (Y.obj j).right)
  let : KanComplex (CosimplicialTotalization.obj (X ⋙ PointedSimplicialSet.forget)) :=
    inferInstanceAs (KanComplex (PointedTotalization.obj X).right)
  let : KanComplex (CosimplicialTotalization.obj (Y ⋙ PointedSimplicialSet.forget)) :=
    inferInstanceAs (KanComplex (PointedTotalization.obj Y).right)
  exact CosimplicialTotalization.map_piIsomorphism
    (Functor.whiskerRight f PointedSimplicialSet.forget) hX hY hf
    (fun j ↦ PointedSimplicialSet.basepoint (X.obj j))

end

end SerrePositivity.KST.Spectra
