module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolutionRestriction
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingNaturality
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.HornCochainContraction

/-!
概要：cell 源の実乗法的写像の全標準ホーンを厳密に充填する。
方針：E2 の元のホーン擬同型を実 AW 制限へ移し、cell の持ち上げを全単体へ戻す。
規約：全係数環・全ホーン位置。SSet のモデル構造や Kan 性を入力しない。
使われ方：元の乗法的写像単体の Kan 性と導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) (n : ℕ) (i : Fin (n + 2))

def hornConvolutionRestriction :
    (simplicialConvolution R B).obj (op (Δ[n + 1] : SSet.{0})) ⟶
      (simplicialConvolution R B).obj (op (SSet.horn (n + 1) i)) :=
  (simplicialConvolution R B).map (SSet.horn (n + 1) i).ι.op

lemma hornConvolutionRestriction_fibration :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (hornConvolutionRestriction R B n i).hom :=
  simplicialConvolution_restriction_fibration R B (SSet.horn (n + 1) i).ι

lemma hornConvolutionRestriction_quasiIso :
    QuasiIso (hornConvolutionRestriction R B n i).hom :=
  simplicialConvolution_restriction_quasiIso R B (SSet.horn (n + 1) i).ι
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalizedHornInclusion_quasiIso R n i)

lemma exists_cellResolution_horn_lift
    (a : cellResolution R A ⟶
      (simplicialConvolution R B).obj (op (SSet.horn (n + 1) i))) :
    ∃ b : cellResolution R A ⟶ (simplicialConvolution R B).obj (op (Δ[n + 1] : SSet.{0})),
      b ≫ hornConvolutionRestriction R B n i = a :=
  exists_cellResolutionArbitraryLift R (hornConvolutionRestriction R B n i)
    (hornConvolutionRestriction_fibration R B n i) (hornConvolutionRestriction_quasiIso R B n i) a

lemma multiplicativeCellMapping_smallHorn_extension
    (a : SSet.uliftFunctor.{u, 0}.obj (SSet.horn (n + 1) i) ⟶
      multiplicativeMappingSimplices R (cellResolution R A) B) :
    ∃ b : SSet.uliftFunctor.{u, 0}.obj (Δ[n + 1] : SSet.{0}) ⟶
        multiplicativeMappingSimplices R (cellResolution R A) B,
      SSet.uliftFunctor.{u, 0}.map (SSet.horn (n + 1) i).ι ≫ b = a := by
  obtain ⟨b, hb⟩ := exists_cellResolution_horn_lift R A B n i
    (smallMultiplicativeMappingTranspose R a)
  refine ⟨smallMultiplicativeMappingCurry R b, ?_⟩
  unfold hornConvolutionRestriction at hb
  rw [smallMultiplicativeMappingCurry_precompose, hb, smallMultiplicativeMappingCurry_transpose]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
