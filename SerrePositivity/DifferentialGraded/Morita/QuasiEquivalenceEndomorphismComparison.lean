module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalenceTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedEquivalenceCompactGenerator

/-! # U16bとU14の実際のtensor–Hom比較の接続

擬同値に沿う延長の後に、指定したU14生成元のHomを取る。逆はU14のtensorの後の制限。
元のU14のthick生成・compact生成仮定を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (hF : QuasiEquivalence F) (G : PerfectDGModule A E)
  (hgen : endomorphismThickGeneratesPerfect A E Set.univ G)

local instance moritaQuasiEquivalenceEndomorphismComparisonLocal1 :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal2 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal3 :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal4 :
    (quasiEquivalencePerfectRestriction A D E F hF).CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal5 :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal6 :
    (endomorphismDerivedHom A E G.val G.property.1).CommShift ℤ :=
  endomorphismDerivedHomCommShift A E G.val G.property.1
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal7 :
    (endomorphismDerivedTensor A E G.val).CommShift ℤ :=
  endomorphismDerivedTensorCommShift A E G.val G.property.1
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal8 :
    (perfectEndomorphismHomToPerfect A E Set.univ G hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A E Set.univ G hgen
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal9 :
    (perfectEndomorphismEquivalence A E Set.univ G hgen).functor.CommShift ℤ :=
  perfectEndomorphismHomCommShift A E Set.univ G hgen
local instance moritaQuasiEquivalenceEndomorphismComparisonLocal10 :
    (perfectEndomorphismTensorToPerfect A E Set.univ G).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A E Set.univ G

def quasiEquivalenceEndomorphismPerfectEquivalence :
    PerfectModuleCategory A D ≌ PerfectModuleCategory A (EndomorphismObject G.val) :=
  (quasiEquivalencePerfectEquivalence A D E F hF).trans
    (perfectEndomorphismEquivalence A E Set.univ G hgen)

instance quasiEquivalenceEndomorphismPerfectFunctorCommShift :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.CommShift ℤ := by
  change (quasiEquivalencePerfectExtension A D E F ⋙
    perfectEndomorphismHomToPerfect A E Set.univ G hgen).CommShift ℤ
  infer_instance

lemma quasiEquivalenceEndomorphismPerfectFunctorIsTriangulated :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.IsTriangulated := by
  let := quasiEquivalencePerfectExtensionIsTriangulated A D E F
  let := perfectEndomorphismHomIsTriangulated A E Set.univ G hgen
  change (quasiEquivalencePerfectExtension A D E F ⋙
    perfectEndomorphismHomToPerfect A E Set.univ G hgen).IsTriangulated
  infer_instance

def quasiEquivalenceEndomorphismPerfectHomSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor ⋙
        perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙
        (dgDerivedExtension A D E F ⋙ endomorphismDerivedHom A E G.val G.property.1) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectEndomorphismHomInclusionIso A E Set.univ G hgen) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quasiEquivalencePerfectExtensionInclusionIso A D E F) _ ≪≫
    Functor.associator _ _ _

lemma quasiEquivalenceEndomorphismPerfectHomSquareCommShift :
    NatTrans.CommShift
      (quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen).hom ℤ := by
  let := perfectEndomorphismHomInclusionIso_commShift A E Set.univ G hgen
  let := quasiEquivalencePerfectExtensionInclusionCommShift A D E F
  dsimp only [quasiEquivalenceEndomorphismPerfectHomSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

def quasiEquivalenceEndomorphismPerfectHomTriangleSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor.mapTriangle ⋙
        (perfectModuleInclusion A (EndomorphismObject G.val) Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D Set.univ).mapTriangle ⋙
        (dgDerivedExtension A D E F ⋙
          endomorphismDerivedHom A E G.val G.property.1).mapTriangle := by
  let := quasiEquivalenceEndomorphismPerfectHomSquareCommShift A D E F hF G hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen) ≪≫
    Functor.mapTriangleCompIso _ _

/-- 合成同値の逆は、元のU14再構成tensorの後に実際の制限を適用する経路と同型。 -/
def quasiEquivalenceEndomorphismPerfectTensorInverseIso :
    perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF ≅
      (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).inverse :=
  Functor.isoWhiskerRight (perfectEndomorphismTensorInverseIso A E Set.univ G hgen) _

def quasiEquivalenceEndomorphismPerfectTensorSquare :
    (perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF) ⋙
        perfectModuleInclusion A D Set.univ ≅
      perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ⋙
        (endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismTensorInclusionIso A E Set.univ G) _ ≪≫
    Functor.associator _ _ _

omit hgen in
lemma quasiEquivalenceEndomorphismPerfectTensorSquareCommShift :
    NatTrans.CommShift
      (quasiEquivalenceEndomorphismPerfectTensorSquare A D E F hF G).hom ℤ := by
  let := perfectEndomorphismTensorInclusionIso_commShift A E Set.univ G
  let := quasiEquivalencePerfectRestrictionInclusionCommShift A D E F hF
  dsimp only [quasiEquivalenceEndomorphismPerfectTensorSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

omit hgen in
def quasiEquivalenceEndomorphismPerfectTensorTriangleSquare :
    (perfectEndomorphismTensorToPerfect A E Set.univ G ⋙
        quasiEquivalencePerfectRestriction A D E F hF).mapTriangle ⋙
        (perfectModuleInclusion A D Set.univ).mapTriangle ≅
      (perfectModuleInclusion A (EndomorphismObject G.val) Set.univ).mapTriangle ⋙
        (endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F).mapTriangle := by
  let := quasiEquivalenceEndomorphismPerfectTensorSquareCommShift A D E F hF G
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalenceEndomorphismPerfectTensorSquare A D E F hF G) ≪≫
    Functor.mapTriangleCompIso _ _

variable (hCG : endomorphismCompactGenerator A E G.val)

/-- U14cの全導来同値との合成。compact生成仮定を省略しない。 -/
def quasiEquivalenceEndomorphismDerivedEquivalence :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A (EndomorphismObject G.val) :=
  (dgFunctorDerivedEquivalence A D E F hF).trans
    (endomorphismDerivedEquivalence_ofCompactGenerator A E Set.univ G hgen hCG).symm

lemma quasiEquivalenceEndomorphismDerivedEquivalence_functor :
    (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).functor =
      dgDerivedExtension A D E F ⋙ endomorphismDerivedHom A E G.val G.property.1 := rfl

lemma quasiEquivalenceEndomorphismDerivedEquivalence_inverse :
    (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).inverse =
      endomorphismDerivedTensor A E G.val ⋙ dgDerivedRestriction A D E F := rfl

def quasiEquivalenceEndomorphismDerivedPerfectSquare :
    (quasiEquivalenceEndomorphismPerfectEquivalence A D E F hF G hgen).functor ⋙
        perfectModuleInclusion A (EndomorphismObject G.val) Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙
        (quasiEquivalenceEndomorphismDerivedEquivalence A D E F hF G hgen hCG).functor :=
  quasiEquivalenceEndomorphismPerfectHomSquare A D E F hF G hgen

end SerrePositivity.DifferentialGraded
