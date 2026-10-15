module
public import SerrePositivity.DifferentialGraded.Module.HomFunctor

/-! # 元の加群型の全Homに値を持つ通常射の前後合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群射の評価を元の複体型の間の射として固定する。 -/
def moduleMorphismComponent (M N : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) (x : D) :
    M.obj (op x) ⟶ N.obj (op x) :=
  (moduleEvaluation A D x).map f

/-- MathlibのHom後合成を元の加群型の主Hom間の射として公開する。 -/
def moduleHomPostcompose (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A) P) :
    moduleHom A D M N ⟶ moduleHom A D M P :=
  eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) M) f

/-- MathlibのHom前合成を元の加群型の主Hom間の射として公開する。 -/
def moduleHomPrecompose (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) :
    moduleHom A D N P ⟶ moduleHom A D M P :=
  eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) P)

@[reassoc]
lemma moduleHomPostcompose_π (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A) P) (x : D) :
    moduleHomPostcompose A D M N P f ≫ moduleHomπ A D M P x =
    moduleHomπ A D M N x ≫ homPostcompose (M.obj (op x))
      (moduleMorphismComponent A D N P f x) :=
  moduleHomWhiskerLeft_π A D f x

@[reassoc]
lemma moduleHomPrecompose_π (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) (x : D) :
    moduleHomPrecompose A D M N P f ≫ moduleHomπ A D M P x =
    moduleHomπ A D N P x ≫ homPrecompose (moduleMorphismComponent A D M N f x) (P.obj (op x)) :=
  moduleHomWhiskerRight_π A D f x

end SerrePositivity.DifferentialGraded
