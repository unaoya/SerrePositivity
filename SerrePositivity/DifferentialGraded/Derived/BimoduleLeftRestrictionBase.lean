module
public import SerrePositivity.DifferentialGraded.Tensor.ComposeLeftRestriction
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLeftRestriction
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso

/-! # 外側左制限と固定K-flat後因子による導来合成の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] (D : Type t) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側左制限の交換を、任意の閉零前因子に自然な同型に束ねる。 -/
def composeWithLeftRestrictionIso (Q : BimoduleCategory A C E) :
    composeWith A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q) ≅
      composeWith A B C E Q ⋙ BimoduleCategory.middleLeftRestrictionFunctor A B E D F :=
  NatIso.ofComponents (fun P => composeLeftRestrictionIso A B C E D F P Q) (by
    intro P P' f
    change composeMap A B C D f
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q)) ≫
        (composeLeftRestrictionIso A B C E D F P' Q).hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E f (𝟙 Q))
    have h := composeLeftRestrictionIso_naturality A B C E D F f (𝟙 Q)
    simpa only [CategoryTheory.Functor.map_id] using h)

/-- 外側左制限の交換同型は、後因子の任意の閉零射にも自然。 -/
lemma composeWithLeftRestrictionIso_naturality
    {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    composeWithMap A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeWithLeftRestrictionIso A B C E D F Q').hom =
      (composeWithLeftRestrictionIso A B C E D F Q).hom ≫
        whiskerRight (composeWithMap A B C E g)
          (BimoduleCategory.middleLeftRestrictionFunctor A B E D F) := by
  apply NatTrans.ext
  funext P
  change composeMap A B C D (𝟙 P)
        ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeLeftRestrictionIso A B C E D F P Q').hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E (𝟙 P) g)
  exact composeLeftRestrictionIso_naturality A B C E D F (𝟙 P) g

variable [Small.{u} E] [Small.{u} D]

/-- 閉零前因子上の比較を、既存の出力側導来制限へ接続する。 -/
def composeWithLeftRestrictionLocalizedIso (Q : BimoduleCategory A C E) :
    composeWith A B C D ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).obj Q) ⋙
        bimoduleToDerived A B D ≅
      composeWith A B C E Q ⋙ bimoduleToDerived A B E ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  Functor.isoWhiskerRight (composeWithLeftRestrictionIso A B C E D F Q)
      (bimoduleToDerived A B D) ≪≫
    Functor.isoWhiskerLeft (composeWith A B C E Q) (middleLeftRestrictionDerivedIso A B E D F)

/-- 固定右K-flat後因子について、局所化前に構成する前合成比較。 -/
def derivedComposeWithLeftRestrictionPreIso (Q : RightKFlatBimoduleCategory A C E) :
    bimoduleToDerived A B C ⋙
        derivedComposeWith A B C D ((rightKFlatLeftRestriction A C E D F).obj Q).obj
          ((rightKFlatLeftRestriction A C E D F).obj Q).property ≅
      bimoduleToDerived A B C ⋙ (derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) :=
  eqToIso (derivedComposeWith_fac A B C D _
      ((rightKFlatLeftRestriction A C E D F).obj Q).property) ≪≫
    composeWithLeftRestrictionLocalizedIso A B C E D F Q.obj ≪≫
    Functor.isoWhiskerRight (eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)).symm
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 前因子は全導来圏、後因子は任意の指定右K-flatモデルにおける外側左制限の比較。 -/
def derivedComposeWithLeftRestrictionIso (Q : RightKFlatBimoduleCategory A C E) :
    derivedComposeWith A B C D ((rightKFlatLeftRestriction A C E D F).obj Q).obj
        ((rightKFlatLeftRestriction A C E D F).obj Q).property ≅
      derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (derivedComposeWithLeftRestrictionPreIso A B C E D F Q)

lemma derivedComposeWithLeftRestrictionIso_hom_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithLeftRestrictionPreIso A B C E D F Q).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded.BimoduleTensor
