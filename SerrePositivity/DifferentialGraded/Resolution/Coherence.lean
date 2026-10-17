module
public import SerrePositivity.DifferentialGraded.Resolution.Bimodule

/-! # 指定dg圏解像度上の五角恒等式 -/
@[expose] public section
noncomputable section
universe u v w z t x v' w' z' t' x'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w} {E : Type z}
  {F : Type t} {G : Type x}
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]

/-- 元のdg圏のHomにflat性を要求せず、指定解像度上の全導来因子で五角が可換。 -/
lemma pentagon (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (S : KFlatDGResolution.{u, t, t'} A F) (T : KFlatDGResolution.{u, x, x'} A G)
    (X : DerivedCategory A Q R) (Y : DerivedCategory A R S) (Z : DerivedCategory A S T) :
    derivedBimodulePentagonShort A P.source Q.source R.source S.source T.source
        R.homKFlat S.homKFlat T.homKFlat X Y Z =
      derivedBimodulePentagonLong A P.source Q.source R.source S.source T.source
        R.homKFlat S.homKFlat T.homKFlat X Y Z :=
  derivedBimodulePentagon A P.source Q.source R.source S.source T.source
    R.homKFlat S.homKFlat T.homKFlat X Y Z

end SerrePositivity.DifferentialGraded.ResolutionBimodule
