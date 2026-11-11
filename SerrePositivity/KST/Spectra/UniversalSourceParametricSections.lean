module

public import SerrePositivity.KST.Spectra.UniversalSourceInterval
public import SerrePositivity.KST.Spectra.PointedParametricPost
public import SerrePositivity.KST.Spectra.PostMappingLifts
public import SerrePositivity.KST.Spectra.PointedTrivialVerticalPaths

/-!
概要：普遍区間の二つの延長切断を、同じ射の全パラメータ族に沿って実区間で比較する。
方針：パラメータを内部 Hom に保持し、同じ anodyne 制限の RLP をその内部 Hom へ移す。
規約：射の族の各頂点で選び直さない。使われ方：普遍交換区間の全 Hom パラメータ自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.UniversalSourceInterval
variable (I : UniversalSourceInterval.{u})

/-- 同じ単位への制限を、全パラメータを保持する内部 Hom へ移した実射。 -/
def parametricRestriction (P Z' : PointedSimplicialSet.{u}) :=
  PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z')

/-- 全パラメータを保持した同じ単位制限も、全単射 RLP を持つ。 -/
lemma parametricRestriction_rlp (P Z' : PointedSimplicialSet.{u}) [KanComplex Z'.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (parametricRestriction I P Z').right :=
  PointedMapping.post_rlp_monomorphisms P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z')
    (universalRestriction_rlp I Z')

variable {P Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : P ⟶ PointedObject.basedHom Z Z')

/-- 元の源で延長してから、同じ標的射の族を後合成する実族。 -/
def parametricExtensionLeft := extensionSection I Z ≫ PointedMapping.parametricPost I.target v

/-- 同じ標的射の族を後合成してから、元の標的で延長する実族。 -/
def parametricExtensionRight := PointedMapping.parametricPost I.source v ≫
  PointedObject.basedHomMap P (extensionSection I Z')

omit [KanComplex Z'.right] in
/-- 前者の射影は元の同じ後合成族に全単体で厳密一致する。 -/
lemma parametricExtensionLeft_projection :
    parametricExtensionLeft I v ≫ parametricRestriction I P Z' =
      PointedMapping.parametricPost I.source v := by
  rw [parametricExtensionLeft, parametricRestriction, Category.assoc,
    PointedMapping.parametricPost_restrict, ← Category.assoc,
    extensionSection_condition, Category.id_comp]

omit [KanComplex Z.right] in
/-- 後者の射影も元の同じ後合成族に全単体で厳密一致する。 -/
lemma parametricExtensionRight_projection :
    parametricExtensionRight I v ≫ parametricRestriction I P Z' =
      PointedMapping.parametricPost I.source v := by
  have h : PointedObject.basedHomMap P (extensionSection I Z') ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z') =
    𝟙 (PointedObject.basedHom P (PointedObject.basedHom I.source Z')) := by
    change (ihom P).map (extensionSection I Z') ≫
      (ihom P).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z') = _
    rw [← CategoryTheory.Functor.map_comp, extensionSection_condition,
      CategoryTheory.Functor.map_id]
    simp only [PointedObject.ihom_obj_eq_basedHom]
  change (PointedMapping.parametricPost I.source v ≫
    PointedObject.basedHomMap P (extensionSection I Z')) ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z') = _
  rw [Category.assoc, h, Category.comp_id]

/-- 同じ全パラメータ族を射影全体で固定する、二つの元の延長切断の実比較区間。 -/
def parametricSectionComparison :
    PointedMapping.VerticalPath (parametricRestriction I P Z')
      (parametricExtensionLeft I v) (parametricExtensionRight I v) :=
  PointedMapping.verticalPathOfRlp (parametricRestriction I P Z')
    (parametricRestriction_rlp I P Z') (parametricExtensionLeft I v) (parametricExtensionRight I v)
    ((parametricExtensionLeft_projection I v).trans (parametricExtensionRight_projection I v).symm)

/-- 比較区間の射影全体は、元の同じ射の族による後合成で一定。 -/
lemma parametricSectionComparison_over :
    (parametricSectionComparison I v).path ≫
        (PointedObject.basedHomMap (PointedObject.basedHom I.source Z)
          (parametricRestriction I P Z')).right =
      SSet.const (PointedMapping.familyVertex (PointedMapping.parametricPost I.source v)) :=
  (parametricSectionComparison I v).over.trans
    (congrArg (fun f => SSet.const (PointedMapping.familyVertex f))
      (parametricExtensionLeft_projection I v))

end SerrePositivity.KST.Spectra.UniversalSourceInterval
