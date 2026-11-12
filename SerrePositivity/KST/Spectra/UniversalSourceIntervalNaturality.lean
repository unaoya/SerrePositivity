module

public import SerrePositivity.KST.Spectra.UniversalSourceInterval
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary
public import SerrePositivity.KST.Spectra.PointedIntervalNaturality

/-!
概要：同じ普遍交換区間の全標的への移送に、両端境界を固定する自然性正方形を与える。
方針：射影固定の切断比較を同じ普遍区間へ作用させ、前後合成の座標をそろえる。
規約：区間や切断を再選択しない。使われ方：loop 値の交換符号区間の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.UniversalSourceInterval
variable (I : UniversalSourceInterval.{u})

/-- 普遍区間の両端を、同じ単位への制限を経由する厳密な族で表示する。 -/
def factoredUniversalInterval (Z : PointedSimplicialSet.{u}) :
    PointedMapping.VerticalPath (PointedObject.toPoint (PointedObject.basedHom I.source Z))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z) :=
  (I.path.basedPre Z).changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp I.first I.unit Z)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp I.second I.unit Z)

/-- 因子表示に直しても、元の同じ普遍区間の辺全体を保持する。 -/
lemma factoredUniversalInterval_path (Z : PointedSimplicialSet.{u}) :
    (factoredUniversalInterval I Z).path = (I.path.basedPre Z).path := rfl

variable {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : Z ⟶ Z')

/-- 同じ切断比較を同じ普遍区間へ作用させた、元の二次元正方形。 -/
def naturalityInputSquare :=
  PointedMapping.VerticalPath.inputSquare (extensionSectionNaturalityInterval I v)
    (factoredUniversalInterval I Z')

omit [KanComplex Z'.right] in
/-- 始辺は元の標的後合成を施した全族交換区間に厳密一致する。 -/
lemma naturalityInput_zero :
    ((interval I Z).basedPost (PointedObject.basedHomMap I.source v)).path =
      ((factoredUniversalInterval I Z').pre
        (extensionSection I Z ≫ PointedObject.basedHomMap I.target v)).path := by
  let P := I.path.basedPre Z
  let P' := I.path.basedPre Z'
  let s := extensionSection I Z
  let r := PointedObject.basedHomMap I.target v
  let t := PointedObject.basedHomMap I.source v
  change (interval I Z).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom I.source Z) t).right =
    (factoredUniversalInterval I Z').path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (s ≫ r) (PointedObject.basedHom I.source Z')).right
  rw [interval_path, factoredUniversalInterval_path]
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s
      (PointedObject.basedHom I.source Z)).right) ≫ _ = _
  have hs := (MonoidalClosed.pre s).naturality t
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change PointedObject.basedHomMap (PointedObject.basedHom I.target Z) t ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s (PointedObject.basedHom I.source Z') =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s (PointedObject.basedHom I.source Z) ≫
      PointedObject.basedHomMap (PointedObject.basedHom I.source Z) t at hs
  have h₀ := congrArg (fun q => P.path ≫ q.right) hs.symm
  have hn := I.path.basedPre_post_path v
  change P.path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom I.target Z) t).right =
    P'.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom I.source Z')).right at hn
  have h₁ := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s
    (PointedObject.basedHom I.source Z')).right) hn
  have h₂ := congrArg (fun q => P'.path ≫ q.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp s r (PointedObject.basedHom I.source Z'))
  simpa only [Under.comp_right, Category.assoc] using h₀.trans (h₁.trans h₂)

omit [KanComplex Z.right] in
/-- 終辺も、元の入力への前合成を施した同じ全族交換区間に厳密一致する。 -/
lemma naturalityInput_one :
    ((interval I Z').pre (PointedObject.basedHomMap I.source v)).path =
      ((factoredUniversalInterval I Z').pre
        (PointedObject.basedHomMap I.source v ≫ extensionSection I Z')).path := by
  change (interval I Z').path ≫ _ = (factoredUniversalInterval I Z').path ≫ _
  rw [interval_path, factoredUniversalInterval_path]
  change ((I.path.basedPre Z').path ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (extensionSection I Z')
      (PointedObject.basedHom I.source Z')).right) ≫ _ = _
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => (I.path.basedPre Z').path ≫ q.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp (PointedObject.basedHomMap I.source v)
        (extensionSection I Z') (PointedObject.basedHom I.source Z'))

/-- 全写像族の交換区間の、同じ二次元自然性正方形。 -/
def naturalitySquare :
    SSet.Homotopy
      (((interval I Z).basedPost (PointedObject.basedHomMap I.source v)).path)
      (((interval I Z').pre (PointedObject.basedHomMap I.source v)).path) where
  h := (naturalityInputSquare I v).h
  h₀ := (naturalityInputSquare I v).h₀.trans (naturalityInput_zero I v).symm
  h₁ := (naturalityInputSquare I v).h₁.trans (naturalityInput_one I v).symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Z'.right] in
/-- 元の切断比較の始点射影は、同じ標的後合成に厳密一致する。 -/
lemma extensionSectionNaturality_source_projection :
    (extensionSection I Z ≫ PointedObject.basedHomMap I.target v) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z' = PointedObject.basedHomMap I.source v := by
  rw [Category.assoc, universalRestriction_post, ← Category.assoc,
    extensionSection_condition, Category.id_comp]

/-- 自然性正方形の左辺全体は、交換後の同じ厳密な頂点で一定。 -/
lemma naturalitySquare_start :
    SquareAdjustment.leftSide ≫ (naturalitySquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedObject.basedHomMap I.source v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z')) := by
  change SquareAdjustment.leftSide ≫
    (PointedMapping.VerticalPath.inputSquare (extensionSectionNaturalityInterval I v)
      (factoredUniversalInterval I Z')).h = _
  rw [PointedMapping.VerticalPath.inputSquare_start_factored,
    extensionSectionNaturality_source_projection]

/-- 自然性正方形の右辺全体も、反転後の同じ厳密な頂点で一定。 -/
lemma naturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (naturalitySquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedObject.basedHomMap I.source v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z')) := by
  change SquareAdjustment.rightSide ≫
    (PointedMapping.VerticalPath.inputSquare (extensionSectionNaturalityInterval I v)
      (factoredUniversalInterval I Z')).h = _
  rw [PointedMapping.VerticalPath.inputSquare_finish_factored,
    extensionSectionNaturality_source_projection]

end SerrePositivity.KST.Spectra.UniversalSourceInterval
