module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftComparison

/-!
概要：全厳密 cone shift 比較を同じ実 cone shift 逆同型へ照合する。
方針：元入力射の回収だけで cone を輸送し、元 descent の二成分を保持する。
規約：元実逆同型を変更しない。
使われ方：実逆回転全比較の cone shift 因子の成分認証。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma shiftedDescRecovery {M N : ModuleCategory R D} (s : ℤ) (f : M ⟶ N)
    (g : moduleShiftObj R D s M ⟶ moduleShiftObj R D s N)
    (q : moduleShiftObj R D s N ⟶ moduleShiftObj R D s (moduleCone R D f))
    (eg : g = moduleShiftMap R D s f)
    (eq : q = moduleShiftMap R D s (moduleConeInr R D f))
    (h : (moduleHom R D (shiftModule s (ForgetEnrichment.to (Complex R) M))
      (shiftModule s (ForgetEnrichment.to (Complex R) (moduleCone R D f)))).d (-1) 0
      (moduleConeShiftLeftInput R D s f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (g ≫ q))).val) :
    moduleConeDescOfBoundary R D g (moduleConeShiftLeftInput R D s f) q h =
      (eqToIso (congrArg (fun t => moduleCone R D t) eg)).hom ≫
        (moduleConeShiftIso R D s f).inv := by
  cases eg
  cases eq
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rfl

variable {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "S" => moduleShiftDG R D
local notation "CS" => fun s : ℤ => dgModuleNaturalConeFunctor R D (F.comp (S s)) (G.comp (S s))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s))

/-- 概要：同じ cone shift 全比較の始域を元 shift 射の実 cone へ戻す指定同型。
方針：元全比較の閉 shift 射回収だけで輸送する。
規約：元 cone 入力を保持。使われ方：元実 shift 逆射の成分回収。 -/
def dgModuleNaturalConeShiftComparisonInputIso (s : ℤ) (x : P) :
    ForgetEnrichment.of (Complex R) ((CS s).obj x) ≅
      moduleCone R D (moduleShiftMap R D s (dgModuleNaturalConeArrow R D F G η x)) :=
  eqToIso (congrArg (fun t => moduleCone R D t)
    (dgModuleNaturalConeShiftArrow R D F G η s x))

/-- 概要：元 cone shift 全比較の閉射は元実逆同型を同じ入力同型で輸送した射。
方針：同じ descent の全閉射と元 shift 入力・右包含を回収する。
規約：元指定二成分を保持。使われ方：全比較の同値性と指定境界。 -/
lemma dgModuleNaturalConeShiftComparison_arrow (s : ℤ) (x : P) :
    dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s))
      (dgModuleNaturalConeShiftComparison R D F G η s) x =
      (dgModuleNaturalConeShiftComparisonInputIso R D F G η s x).hom ≫
        (moduleConeShiftIso R D s (dgModuleNaturalConeArrow R D F G η x)).inv := by
  exact (dgModuleNaturalConeDesc_arrow R D (F.comp (S s)) (G.comp (S s)) ((CF).comp (S s))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) (S s))
    (dgModuleNaturalConeShiftNull R D F G η s)
    (dgModuleNaturalConeShiftComparison_boundary R D F G η s)
    (dgModuleNaturalConeShiftNull_naturality R D F G η s) x).trans
      (shiftedDescRecovery R D s (dgModuleNaturalConeArrow R D F G η x) _ _
        (dgModuleNaturalConeShiftArrow R D F G η s x)
        ((dgModuleNaturalConeShiftArrow R D G (CF) (ν) s x).trans
          (congrArg (moduleShiftMap R D s) (dgModuleNaturalConeInr_arrow R D F G η x)))
        (dgModuleNaturalConeShiftComparison_boundary R D F G η s x))
end SerrePositivity.KST.SConstruction
