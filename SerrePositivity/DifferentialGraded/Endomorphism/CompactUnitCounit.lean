module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.CompactGenerator

/-! # Perf上の単位・余単位と、外部入力compact⇒Perfの利用

U13dは実装しない。compact⇒Perfを使う場合は明示した入力として受け取る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma endomorphismDerivedUnit_isIso_onPerfect
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N.obj) := by
  have := perfectEndomorphismUnit_isIso A D S E hgen
  rw [← perfectEndomorphismUnit_inclusion A D S E hgen N]
  infer_instance

lemma endomorphismDerivedCounit_isIso_onPerfect (M : PerfectModuleCategoryOver A D S) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app M.obj) := by
  have := perfectEndomorphismCounit_isIso A D S E hgen
  rw [← perfectEndomorphismCounit_inclusion A D S E hgen M]
  infer_instance

/-- End側のcompact⇒Perfは外部から受け取る証拠として明示する。 -/
lemma endomorphismDerivedUnit_isIso_of_compact
    (compactToPerfect : ∀ N : DerivedModuleCategory A (EndomorphismObject E.val),
      moduleCompact A (EndomorphismObject E.val) N →
        modulePerfect A (EndomorphismObject E.val) N)
    (N : DerivedModuleCategory A (EndomorphismObject E.val))
    (hN : moduleCompact A (EndomorphismObject E.val) N) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_onPerfect A D S E hgen ⟨N, compactToPerfect N hN⟩

/-- 指定Sに対するcompact⇒Perf_Sも、自動推論せず外部の証拠として受け取る。 -/
lemma endomorphismDerivedCounit_isIso_of_compact
    (compactToPerfect : ∀ M : DerivedModuleCategory A D,
      moduleCompact A D M → modulePerfectOver A D S M)
    (M : DerivedModuleCategory A D) (hM : moduleCompact A D M) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app M) :=
  endomorphismDerivedCounit_isIso_onPerfect A D S E hgen ⟨M, compactToPerfect M hM⟩

end SerrePositivity.DifferentialGraded
