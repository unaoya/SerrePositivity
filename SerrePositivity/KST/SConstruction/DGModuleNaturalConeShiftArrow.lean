module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransWhisker
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：元全厳密比較の dg shift が同じ実加群 shift 射を保つことを示す。
方針：元閉射の cycle と dg 後合成の cycle を比較する。
規約：実 shift 射の選択を変えない。
使われ方：実逆回転 cone 合成全比較の逆 shift。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：同じ dg shift 後の全比較の閉成分は元成分の実加群 shift。
方針：閉射・閉元対応と元 dg shift の閉零回収を使う。
規約：元実射と元次数を保持。使われ方：同じ実逆 shift 全比較の成分。 -/
lemma dgModuleNaturalConeShiftArrow (s : ℤ) (x : P) :
    dgModuleNaturalConeArrow R D (F.comp (moduleShiftDG R D s))
      (G.comp (moduleShiftDG R D s))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (moduleShiftDG R D s)) x =
        moduleShiftMap R D s (dgModuleNaturalConeArrow R D F G η x) := by
  refine Eq.trans ?_ (moduleShiftDG_map_eq R D s _)
  apply (closedHomEquiv R (RightModule R D) _ _).injective
  apply Subtype.ext
  exact (dgModuleNaturalConeArrow_cycle R D _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (moduleShiftDG R D s)) x).trans
      ((congrArg (((moduleShiftDG R D s).map (F.obj x) (G.obj x)).f 0)
        (dgModuleNaturalConeArrow_cycle R D F G η x).symm).trans
          (cycleFromUnit_postcomp _ _).symm)
end SerrePositivity.KST.SConstruction
