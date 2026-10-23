module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaColimitFiniteProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexCoconeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexColimitReflection

/-!
概要：P_Σ の元の sifted 図式の実際の余極限全余錐と、前層圏での同じ余錐を供給する。
方針：元の前層余極限頂点の有限積保存を証明済みの界面で使い、同じ全余錐を制限する。
規約：元の図式・余極限余錐の全単体を保持。底の quasicategory 性は要求しない。
使われ方：HTT 5.5.8 の sifted 余極限閉性と P_Σ の生成・普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}} [IsSiftedInfinity B]
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)

/-- 元の前層余極限全余錐そのものを P_Σ の同じ図式へ制限した、実際の内部余錐。 -/
def sigmaPresheafSiftedColimitCone : JoinCocone r :=
  fullSubcomplexCoconeLift (IsSigmaPresheaf (C := C)) r
    (presheafCoherentColimitCone (r ≫ sigmaPresheafInfinityInclusion C))
    (sigmaPresheafAmbientColimit_isSigmaPresheaf r)

/-- 元の内部余錐を包含すると、実際の前層余極限全余錐を厳密に回収する。 -/
lemma sigmaPresheafSiftedColimitCone_inclusion :
    F1B.kanPostcomposeCocone (sigmaPresheafInfinityInclusion C)
      (sigmaPresheafSiftedColimitCone r) =
      presheafCoherentColimitCone (r ≫ sigmaPresheafInfinityInclusion C) :=
  fullSubcomplexCoconeLift_inclusion _ _ _ _

/-- 元の同じ内部全余錐は P_Σ の余極限余錐である。 -/
lemma sigmaPresheafSiftedColimitCone_isColimit :
    IsColimitCone (sigmaPresheafSiftedColimitCone r) := by
  apply isColimitCone_of_fullSubcomplex (IsSigmaPresheaf (C := C))
  change IsColimitCone (F1B.kanPostcomposeCocone (sigmaPresheafInfinityInclusion C)
    (sigmaPresheafSiftedColimitCone r))
  rw [sigmaPresheafSiftedColimitCone_inclusion]
  exact presheafCoherentColimitCone_isColimit _

/-- 元の内部余極限余錐の包含像そのものも、元の前層圏の余極限余錐。 -/
lemma sigmaPresheafSiftedColimitCone_inclusion_isColimit :
    IsColimitCone (F1B.kanPostcomposeCocone (sigmaPresheafInfinityInclusion C)
      (sigmaPresheafSiftedColimitCone r)) := by
  rw [sigmaPresheafSiftedColimitCone_inclusion]
  exact presheafCoherentColimitCone_isColimit _

/-- 任意の小さい sifted な底上の元の P_Σ 図式は、P_Σ 内に余極限を持つ。 -/
lemma sigmaPresheaf_hasColimit_of_sifted : HasColimit r :=
  ⟨sigmaPresheafSiftedColimitCone r, sigmaPresheafSiftedColimitCone_isColimit r⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
