module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImageComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso

/-!
概要：同じ元 cone の dg 関手像を native 全関手同型で比較する。
方針：元全厳密比較の閉成分を回収し同じ実同型性を使用する。
規約：全ホモトピーと元 cone image 射を保持する。
使われ方：元全実逆回転を同じ realization と固定 ν へ運ぶ評価因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
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

/-- 概要：元 cone image 全比較の cycle は同じ閉成分の cycle。
方針：元閉射・閉元の対応の逆律を使用する。
規約：同じ元全比較。使われ方：指定 native 全比較への束ね。 -/
lemma dgModuleNaturalConeImage_cycle (x : P) :
    (θ).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeArrow R E (CηQ) (CQ) (θ) x)) := by
  apply Subtype.ext
  exact (dgModuleNaturalConeArrow_cycle R E (CηQ) (CQ) (θ) x).symm

/-- 概要：元 cone の同じ dg 関手像を保つ native 全関手同型。
方針：元全厳密ホモトピー・指定閉射・元実同型の三つを束ねる。
規約：成分同値の任意選択を使わない。
使われ方：元 gluing 全実逆回転を実 realization へ運ぶ全比較。 -/
def dgModuleNaturalConeImageNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CηQ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CQ)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R E (F := (CηQ)) (G := (CQ)) (θ)
    (fun x => dgModuleNaturalConeArrow R E (CηQ) (CQ) (θ) x)
    (dgModuleNaturalConeImage_cycle R E D F G η Q)
    (dgModuleNaturalConeImage_isIso R E D F G η Q)
end SerrePositivity.KST.SConstruction
