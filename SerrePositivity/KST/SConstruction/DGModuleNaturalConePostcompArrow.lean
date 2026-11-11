module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftArrow

/-!
概要：同じ全厳密比較の dg 後合成が元実加群射を保持することを示す。
方針：元閉射の cycle と dg 後合成の cycle を比較する。
規約：元実後合成射を保持する。
使われ方：元 gluing 全実逆回転を実 realization へ運ぶ cone 全比較。
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

/-- 概要：元 dg 後合成の全比較は元閉成分の同じ実像を回収する。
方針：閉射・閉元の逆律と元後合成の cycle 保存を使う。
規約：元射の厳密等式。使われ方：同じ実 cone image の入力照合。 -/
lemma dgModuleNaturalConePostcompArrow (x : P) :
    dgModuleNaturalConeArrow R E (F.comp Q) (G.comp Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q) x =
      Q.onClosed.map (dgModuleNaturalConeArrow R D F G η x) := by
  apply (closedHomEquiv R (RightModule R E) _ _).injective
  apply Subtype.ext
  exact (dgModuleNaturalConeArrow_cycle R E _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q) x).trans
    ((congrArg ((Q.map (F.obj x) (G.obj x)).f 0)
      (dgModuleNaturalConeArrow_cycle R D F G η x).symm).trans
        (cycleFromUnit_postcomp _ _).symm)
end SerrePositivity.KST.SConstruction
