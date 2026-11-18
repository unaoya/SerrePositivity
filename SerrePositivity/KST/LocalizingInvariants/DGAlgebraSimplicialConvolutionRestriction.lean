module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolution
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionArbitraryLift
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedMonomorphismCofibration
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveHomotopyInverse
public import SerrePositivity.HomologicalAlgebra.Complexes.HomRestriction

/-!
概要：実 AW 畳み込みの単射への制限は次数別全射で、正規化擬同型なら擬同型。
方針：E2 の元の正規化 cofibration と Hom 制限・鎖ホモトピー逆を適用する。
規約：正規化の擬同型性を勝手に推論せず、同じ元の射に対して用いる。
使われ方：E2 の実標準ホーンの証拠を適用し、cell 源の境界射を持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R))
  {K L : SSet.{0}} (f : K ⟶ L) [Mono f]

lemma simplicialConvolution_restriction_fibration :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R ((simplicialConvolution R B).map f.op).hom := by
  change _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R
    ((MonoidalClosed.pre ((EInfinity.BarrattEccles.normalizedFunctor R).map f)).app B.X)
  rw [convolutionPre_eq_homPrecompose]
  exact _root_.SerrePositivity.HomRestriction.homPrecompose_projectiveFibration _
    (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration R f) B.X

lemma simplicialConvolution_restriction_quasiIso
    (hq : QuasiIso ((EInfinity.BarrattEccles.normalizedFunctor R).map f)) :
    QuasiIso ((simplicialConvolution R B).map f.op).hom := by
  change QuasiIso
    ((MonoidalClosed.pre ((EInfinity.BarrattEccles.normalizedFunctor R).map f)).app B.X)
  rw [convolutionPre_eq_homPrecompose]
  obtain ⟨e, he⟩ := _root_.SerrePositivity.ProjectiveHomotopyInverse.projectiveTrivialCofibration_homotopyEquiv
    ((EInfinity.BarrattEccles.normalizedFunctor R).map f)
    (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration R f) hq
  rw [← he]
  exact (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyEquiv e B.X).quasiIso_hom

lemma exists_cellResolution_restriction_lift (A : Mon (Complex R))
    (hq : QuasiIso ((EInfinity.BarrattEccles.normalizedFunctor R).map f))
    (a : cellResolution R A ⟶ (simplicialConvolution R B).obj (Opposite.op K)) :
    ∃ b : cellResolution R A ⟶ (simplicialConvolution R B).obj (Opposite.op L),
      b ≫ (simplicialConvolution R B).map f.op = a :=
  exists_cellResolutionArbitraryLift R ((simplicialConvolution R B).map f.op)
    (simplicialConvolution_restriction_fibration R B f)
    (simplicialConvolution_restriction_quasiIso R B f hq) a

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
