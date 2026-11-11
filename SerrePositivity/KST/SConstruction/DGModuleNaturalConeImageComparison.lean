module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConeIso

/-!
概要：元 cone image 全比較の閉成分を同じ実 cone image 比較へ回収する。
方針：元入力閉射の回収等号だけで cone を輸送する。
規約：同じ元左包含像・元右包含像を保持する。
使われ方：元 gluing 全実逆回転を realization へ運ぶ全比較の同値性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma imageDescRecovery
    (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
    (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
    (Q : DGFunctor R (RightModule R D) (RightModule R E))
    {M N : ModuleCategory R D} (f : M ⟶ N)
    (g : Q.onClosed.obj M ⟶ Q.onClosed.obj N)
    (q : Q.onClosed.obj N ⟶ Q.onClosed.obj (moduleCone R D f))
    (eg : g = Q.onClosed.map f) (eq : q = Q.onClosed.map (moduleConeInr R D f))
    (ds : (moduleHom R E (Q.obj M) (Q.obj (moduleCone R D f))).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeInl R D E Q f) =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (g ≫ q))).val) :
    moduleConeDescOfBoundary R E g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeInl R D E Q f) q ds =
      (eqToIso (congrArg (fun t => moduleCone R E t) eg)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison R D E Q f := by
  cases eg
  cases eq
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rfl
variable (R : Type u) [CommRing R]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
  (Q : DGFunctor R (RightModule R D) (RightModule R E))
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FQ" => DGFunctor.comp F Q
local notation "GQ" => DGFunctor.comp G Q
local notation "CQ" => DGFunctor.comp (CF) Q
local notation "ηQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "νQ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) Q
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "s" => dgModuleNaturalConeImageInput R E D F G η Q


local notation "CηQ" => dgModuleNaturalConeFunctor R E (FQ) (GQ) (ηQ)
local notation "θ" => dgModuleNaturalConeImage R E D F G η Q

/-- 概要：全 cone image 比較の始域を元実像射の cone へ戻す指定同型。
方針：元後合成閉射の回収等号だけで cone を輸送する。
規約：元実 cone 入力を保持。使われ方：指定実比較射の成分照合。 -/
def dgModuleNaturalConeImageInputIso (x : P) :
    ForgetEnrichment.of (Complex R) ((CηQ).obj x) ≅
      moduleCone R E (Q.onClosed.map (a x)) :=
  eqToIso (congrArg (fun t => moduleCone R E t)
    (dgModuleNaturalConePostcompArrow R E D F G η Q x))

/-- 概要：元全 cone image 比較の閉成分は同じ元実比較射。
方針：元 descent の成分回収と同じ入力・右包含の回収を合成する。
規約：元射を任意の同値で置き換えない。使われ方：全実比較の可逆性認証。 -/
lemma dgModuleNaturalConeImage_arrow (x : P) :
    dgModuleNaturalConeArrow R E (CηQ) (CQ) (θ) x =
      (dgModuleNaturalConeImageInputIso R E D F G η Q x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison R D E Q (a x) := by
  exact (dgModuleNaturalConeDesc_arrow R E (FQ) (GQ) (CQ) (ηQ) (νQ) (s)
    (dgModuleNaturalConeImage_boundary R E D F G η Q)
    (dgModuleNaturalConeImageInput_naturality R E D F G η Q) x).trans
    (imageDescRecovery R E D Q (a x)
      (dgModuleNaturalConeArrow R E (FQ) (GQ) (ηQ) x)
      (dgModuleNaturalConeArrow R E (GQ) (CQ) (νQ) x)
      (dgModuleNaturalConePostcompArrow R E D F G η Q x)
      ((dgModuleNaturalConePostcompArrow R E D G (CF) (ν) Q x).trans
        (congrArg Q.onClosed.map (dgModuleNaturalConeInr_arrow R D F G η x)))
      (dgModuleNaturalConeImage_boundary R E D F G η Q x))

/-- 概要：同じ元全 cone image 比較の閉成分は実加群同型。
方針：元入力輸送同型と D の元実 cone image 同型を合成する。
規約：同じ元閉射の同型性。使われ方：native 全比較の可逆性。 -/
lemma dgModuleNaturalConeImage_isIso (x : P) :
    IsIso (dgModuleNaturalConeArrow R E (CηQ) (CQ) (θ) x) := by
  rw [dgModuleNaturalConeImage_arrow]
  exact Iso.isIso_hom ((dgModuleNaturalConeImageInputIso R E D F G η Q x) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeIso R D E Q (a x))
end SerrePositivity.KST.SConstruction
