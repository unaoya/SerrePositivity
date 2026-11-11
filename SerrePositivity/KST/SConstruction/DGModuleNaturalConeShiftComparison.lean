module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftNull
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeDesc
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：同じ元 cone と整数 shift の実比較を全厳密自然変換へ束ねる。
方針：元 shift 零化入力と右包含を元 cone descent へ渡す。
規約：元 cone shift 逆射の指定二成分を保持する。
使われ方：元実逆回転後の合成全比較の逆 shift。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma shiftBoundary {M N : ModuleCategory R D} (s : ℤ) (f : M ⟶ N)
    (p : moduleShiftObj R D s M ⟶ moduleShiftObj R D s N)
    (q : moduleShiftObj R D s N ⟶ moduleShiftObj R D s (moduleCone R D f))
    (hp : p = moduleShiftMap R D s f)
    (hq : q = moduleShiftMap R D s (moduleConeInr R D f)) :
    (moduleHom R D (shiftModule s (ForgetEnrichment.to (Complex R) M))
      (shiftModule s (ForgetEnrichment.to (Complex R) (moduleCone R D f)))).d (-1) 0
      (moduleConeShiftLeftInput R D s f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (p ≫ q))).val := by
  cases hp
  cases hq
  exact moduleConeShiftLeftInput_d R D s f
variable {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "S" => moduleShiftDG R D

/-- 概要：元全自然な shift 零化入力の微分は元二辺の同じ合成。
方針：元実 cone shift 境界と元実 shift 射の回収を使う。
規約：元の指定零化入力を保持。使われ方：全 cone shift descent の境界。 -/
lemma dgModuleNaturalConeShiftComparison_boundary (s : ℤ) (x : P) :
    (moduleHom R D (shiftModule s (F.obj x)) (shiftModule s ((CF).obj x))).d (-1) 0
      (dgModuleNaturalConeShiftNull R D F G η s x) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeArrow R D (F.comp (S s)) (G.comp (S s))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s)) x ≫
      dgModuleNaturalConeArrow R D (G.comp (S s)) ((CF).comp (S s))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) (S s)) x))).val := by
  dsimp only [dgModuleNaturalConeShiftNull, dgModuleNaturalConeNullHomotopyElement]
  exact shiftBoundary R D s (dgModuleNaturalConeArrow R D F G η x) _ _
    (dgModuleNaturalConeShiftArrow R D F G η s x)
    ((dgModuleNaturalConeShiftArrow R D G (CF) (ν) s x).trans
      (congrArg (moduleShiftMap R D s) (dgModuleNaturalConeInr_arrow R D F G η x)))

/-- 概要：元 cone shift 逆比較の同じ入力を持つ全厳密比較。
方針：元全自然な shift 零化入力・指定右包含を元 descent に渡す。
規約：元二成分を保持。使われ方：実逆回転後の全比較の cone shift 因子。 -/
def dgModuleNaturalConeShiftComparison (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
      (dgModuleNaturalConeFunctor R D (F.comp (S s)) (G.comp (S s))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s))) ((CF).comp (S s)) :=
  dgModuleNaturalConeDesc R D (F.comp (S s)) (G.comp (S s)) ((CF).comp (S s))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) (S s))
    (dgModuleNaturalConeShiftNull R D F G η s)
    (dgModuleNaturalConeShiftComparison_boundary R D F G η s)
    (dgModuleNaturalConeShiftNull_naturality R D F G η s)
end SerrePositivity.KST.SConstruction
