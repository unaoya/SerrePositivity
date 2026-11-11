module

public import SerrePositivity.KST.Spectra.UniversalSourceParametricInput
public import SerrePositivity.KST.Spectra.PointedPrecompositionParametricNaturality

/-!
概要：元の普遍区間の全射族による自然性を、同じ実入力正方形から両端境界固定で回収する。
方針：源側の実辺を前合成区間の豊穣自然性で照合し、標的側の同じ実辺と束ねる。
規約：全パラメータと元の区間・切断を保持。使われ方：通常円の交換族の全 Hom 自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.UniversalSourceInterval
variable (I : UniversalSourceInterval.{u})
  {P Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : P ⟶ PointedObject.basedHom Z Z')

omit [KanComplex Z'.right] in
/-- 始辺は源側の元の同じ普遍区間へ全射族を後合成した実辺そのもの。 -/
lemma parametricInput_zero :
    ((interval I Z).basedPost (PointedMapping.parametricPost I.source v)).path =
      ((parametricFactoredInterval I P Z').pre (parametricExtensionLeft I v)).path := by
  let R := I.path.basedPre Z
  let R' := (I.path.basedPre Z').basedIhomMap P
  let s := extensionSection I Z
  let e := PointedMapping.parametricPost I.target v
  let t := PointedMapping.parametricPost I.source v
  change (interval I Z).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom I.source Z) t).right =
    (parametricFactoredInterval I P Z').path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (s ≫ e)
        (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right
  rw [interval_path, parametricFactoredInterval_path]
  change (R.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s (PointedObject.basedHom I.source Z)).right) ≫
      (PointedObject.basedHomMap (PointedObject.basedHom I.source Z) t).right =
    R'.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (s ≫ e)
      (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right
  have hs := (MonoidalClosed.pre s).naturality t
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change PointedObject.basedHomMap (PointedObject.basedHom I.target Z) t ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s (PointedObject.basedHom P (PointedObject.basedHom I.source Z')) =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s (PointedObject.basedHom I.source Z) ≫
      PointedObject.basedHomMap (PointedObject.basedHom I.source Z) t at hs
  have h₀ := congrArg (fun q => R.path ≫ q.right) hs.symm
  have hn := I.path.basedPre_parametricPost_path v
  change R.path ≫ (PointedObject.basedHomMap (PointedObject.basedHom I.target Z) t).right =
    R'.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e
      (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right at hn
  have h₁ := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s
    (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right) hn
  have h₂ := congrArg (fun q => R'.path ≫ q.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp s e
      (PointedObject.basedHom P (PointedObject.basedHom I.source Z')))
  simpa only [Under.comp_right, Category.assoc] using h₀.trans (h₁.trans h₂)

/-- 元の同じ普遍区間の、射の全パラメータを含む実自然性正方形。 -/
def parametricNaturalitySquare :
    SSet.Homotopy (((interval I Z).basedPost (PointedMapping.parametricPost I.source v)).path)
      ((((interval I Z').basedIhomMap P).pre (PointedMapping.parametricPost I.source v)).path) where
  h := (parametricInputSquare I v).h
  h₀ := (parametricInputSquare I v).h₀.trans (parametricInput_zero I v).symm
  h₁ := (parametricInputSquare I v).h₁.trans (parametricInput_one I v).symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 左境界全体は、同じ射の全族と第一源作用の頂点で一定。 -/
lemma parametricNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (parametricNaturalitySquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedMapping.parametricPost I.source v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z'))) :=
  parametricInputSquare_start I v

/-- 右境界全体も、同じ射の全族と第二源作用の頂点で一定。 -/
lemma parametricNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (parametricNaturalitySquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedMapping.parametricPost I.source v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z'))) :=
  parametricInputSquare_finish I v

end SerrePositivity.KST.Spectra.UniversalSourceInterval
