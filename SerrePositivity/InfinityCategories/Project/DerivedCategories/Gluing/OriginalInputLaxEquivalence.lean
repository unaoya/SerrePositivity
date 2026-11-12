module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OriginalInputLaxLegComparisons
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetDerivedLaxEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackCospanIsoEquivalence
/-!
概要：元 Hom 終域比較を固定入力の元二脚の lax 模型へ接続する。
方針：元終域の実逆と、指定入力同値を保つ cospan 全比較を合成する。
規約：左右射影は全関手同型で指定する。使われ方：K-S• の元二脚供給入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction _root_.SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R A B L
local notation "DR" => DGSmallPerfectArrowTarget R A C G
local notation "V" => DGOdotCorner R d
local notation "P" => dgSmallPerfectSquareLeftMap R A B C E L G p q
local notation "Q" => dgSmallPerfectSquareRightMap R A B C E L G p q

def dgGluingOriginalInputLaxCospanEquivalence :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanIsoEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftLeg R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightLeg R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence

def dgGluingOriginalInputLaxEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgOdotMilnorLaxCategory R d).obj (dgOdotPerfLaxCategory R d).obj :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q).trans
    (dgGluingOriginalInputLaxCospanEquivalence R d)

def dgGluingOriginalInputLaxEquivalence_fst : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgGluingOriginalInputLaxEquivalence R d).hom ≫
      (laxFst (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxLeftInputEquivalence R d).inv) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanIsoEquivalence_fst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftLeg R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightLeg R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp e.hom
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDerivedLaxEquivalence_fst.{u, 0} R CL DR V P Q).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom
  have h := h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₂ (Category.assoc _ _ _) rfl)
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R CL)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom =
        (dgOdotMilnorLaxLeftInputEquivalence R d).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence_input, Iso.inv_hom_id_assoc]
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h ?_ ?_
  · exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hc]; rfl

def dgGluingOriginalInputLaxEquivalence_snd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgGluingOriginalInputLaxEquivalence R d).hom ≫
      (laxSnd (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom)
    ((laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom ≫
      (dgOdotMilnorLaxRightInputEquivalence R d).inv) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanIsoEquivalence_snd (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)
    (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftLeg R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightLeg R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp e.hom
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDerivedLaxEquivalence_snd.{u, 0} R CL DR V P Q).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom
  have h := h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₂ (Category.assoc _ _ _) rfl)
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R DR)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom =
        (dgOdotMilnorLaxRightInputEquivalence R d).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence_input, Iso.inv_hom_id_assoc]
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h ?_ ?_
  · exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hc]; rfl

def dgGluingOriginalLaxComparisonInput : DGOdotMilnorOriginalLaxComparisonInput R d where
  gluing := dgGluingOriginalInputLaxEquivalence R d
  fst := dgGluingOriginalInputLaxEquivalence_fst R d
  snd := dgGluingOriginalInputLaxEquivalence_snd R d

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
