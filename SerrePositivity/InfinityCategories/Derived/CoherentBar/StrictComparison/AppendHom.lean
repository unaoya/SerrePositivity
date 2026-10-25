module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendClosed
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomExchange
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomDegrees

/-!
概要：上界以下の単体に末尾付加し、それ以外では零とする全次数自然な作用素を作る。
方針：実正規化 graded 直和の Hom 同値で、閉じた次数 −1 の列を貼り合わせる。
規約：ここでは内部微分についての閉性だけを示す。
使われ方：有限 support に制限した bar 縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

lemma dgStrictAppendColumn_d {n : ℕ} (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).d (-1) 0
      (dgStrictAppendColumn R D F s b hb) = 0 := by
  unfold dgStrictAppendColumn
  erw [dgStrictHom_postcompose_d R D,
    dgStrictAppendBlock_d R D F s b hb, map_zero]

lemma dgStrictNormalizedHomEquiv_apply (N : RightModule R D) (q : ℤ)
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) N).X q)
    (s : dgCoherentBarNormalizedIndex (nerve J)) :
    dgCoherentBarNormalizedHomEquiv R D (dgCoherentBarStrictDiagram R D F) N q z s =
      (eHomWhiskerRight (Complex R)
        (Sigma.ι (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F)) s)
        (ForgetEnrichment.of (Complex R) N)).f q z :=
  ConcreteCategory.congr_hom (dgModuleCoproductHomDegreeIso_π R D
    (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F))
    (ForgetEnrichment.of (Complex R) N) q s) z

def dgStrictAppendHomColumns (b : J) (s : dgCoherentBarNormalizedIndex (nerve J)) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F) s))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).X (-1) :=
  by
    classical
    exact if hb : s.val.2.obj (Fin.last s.val.1) ≤ b then
      dgStrictAppendColumn R D F s.val.2 b hb else 0

def dgStrictAppendGradedHom (b : J) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).X (-1) :=
  (dgCoherentBarNormalizedHomEquiv R D (dgCoherentBarStrictDiagram R D F)
    (ForgetEnrichment.to (Complex R)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) (-1)).symm
      (dgStrictAppendHomColumns R D F b)

lemma dgStrictAppendGradedHom_restrict (b : J)
    (s : dgCoherentBarNormalizedIndex (nerve J)) :
    (eHomWhiskerRight (Complex R)
      (Sigma.ι (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F)) s)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))).f (-1)
      (dgStrictAppendGradedHom R D F b) = dgStrictAppendHomColumns R D F b s := by
  erw [← dgStrictNormalizedHomEquiv_apply R D F]
  exact congrFun ((dgCoherentBarNormalizedHomEquiv R D (dgCoherentBarStrictDiagram R D F)
    (ForgetEnrichment.to (Complex R)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) (-1)).apply_symm_apply
        (dgStrictAppendHomColumns R D F b)) s

end SerrePositivity.InfinityCategories
