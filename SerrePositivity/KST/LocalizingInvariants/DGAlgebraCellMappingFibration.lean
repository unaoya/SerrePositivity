module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionFibration
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingCellLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingKan

/-!
概要：次数別全射な実代数射は、cell 源の実乗法的写像上で Kan fibration を誘導する。
方針：元の全ホーン平方を相対 AW 制限への境界射へ戻し、実 cell の全段 lift を使う。
規約：両境界は元の全単体の射で、固定点だけの照合に弱めない。
使われ方：Postnikov の全射 class の像と、指定底の相対写像模型の Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) {X B : Mon (Complex R)}
  (q : X ⟶ B) (hq : EInfinity.projectiveFibrations R q.hom)

include hq

lemma multiplicativeCellMapping_smallHorn_lift (n : ℕ) (i : Fin (n + 2))
    (a : SSet.uliftFunctor.{u, 0}.obj (SSet.horn (n + 1) i) ⟶
      multiplicativeMappingSimplices R (cellResolution R A) X)
    (b : SSet.uliftFunctor.{u, 0}.obj (Δ[n + 1] : SSet.{0}) ⟶
      multiplicativeMappingSimplices R (cellResolution R A) B)
    (hab : a ≫ multiplicativeMappingPostcompose R (cellResolution R A) q =
      SSet.uliftFunctor.{u, 0}.map (SSet.horn (n + 1) i).ι ≫ b) :
    ∃ c : SSet.uliftFunctor.{u, 0}.obj (Δ[n + 1] : SSet.{0}) ⟶
        multiplicativeMappingSimplices R (cellResolution R A) X,
      SSet.uliftFunctor.{u, 0}.map (SSet.horn (n + 1) i).ι ≫ c = a ∧
        c ≫ multiplicativeMappingPostcompose R (cellResolution R A) q = b := by
  exact multiplicativeCellMapping_small_lift R A q (SSet.horn (n + 1) i).ι
    (relativeConvolutionRestriction_fibration R q _ hq)
    (relativeConvolutionRestriction_quasiIso R q _
      (EInfinity.AlexanderWhitney.normalizedHornInclusion_quasiIso R n i)) a b hab

lemma multiplicativeCellMapping_fibration :
    Fibration (multiplicativeMappingPostcompose R (cellResolution R A) q) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro _ _ j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  let hsmall : HasLiftingProperty
      (SSet.uliftFunctor.{u, 0}.map (SSet.horn.{0} (n + 1) i).ι)
      (multiplicativeMappingPostcompose R (cellResolution R A) q) := {
    sq_hasLift := fun {a b} sq => by
      obtain ⟨c, ha, hb⟩ := multiplicativeCellMapping_smallHorn_lift R A q hq n i
        a b sq.w
      exact ⟨c, ha, hb⟩ }
  exact HasLiftingProperty.of_arrow_iso_left
    (Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{0, u} (n + 1) i) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{0, u} (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso_ι (n + 1) i))
    (multiplicativeMappingPostcompose R (cellResolution R A) q) (hip := hsmall)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
