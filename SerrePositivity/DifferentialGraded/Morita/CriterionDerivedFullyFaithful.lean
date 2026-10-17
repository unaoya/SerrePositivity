module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedHomLocus
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedGeneration
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionHomGeneration

/-! # Perf上のHom比較を全主導来対象へ広げる二段階の局所化帰納

終域変数はcompactな始域と像のcompact性で、始域変数は余積の普遍性で扱う。
最後の始域帰納には既存の指定射のHom比較補題を恒等射に適用するだけで、
一般右随伴やその存在・unit/counitは使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [T.CommShift ℤ] [T.IsTriangulated]
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
  (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
  (hhom : ∀ (X Y : DerivedModuleCategory A D), modulePerfect A D X →
    modulePerfect A D Y → Function.Bijective (fun f : X ⟶ Y => T.map f))
include hG hcop hperf hhom

/-- 始域がperfectなら、終域のcompact生成から任意終域でHom比較が全単射となる。 -/
lemma criterionDerivedHom_fromPerfect_all (X : DerivedModuleCategory A D)
    (hX : modulePerfect A D X) (Y : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  let P := criterionDerivedHomTargetLocus A D E T X
  have hgen : ∀ i, P (G i) := by
    intro i n
    exact hhom X _ hX (modulePerfect_shift A D (moduleCompact_perfect A D (hG.compact i)) n)
  have hY : P Y := hG.localizing P
    (criterionDerivedHomTargetLocus_coproduct A D E T X hcop
      (modulePerfect_compact A D hX) (modulePerfect_compact A E (hperf X hX))) hgen Y
  exact criterionDerivedHom_target_iso A D E T X
    ((shiftFunctorZero _ ℤ).app Y).symm (hY 0)

/-- 二つ目の帰納を始域に適用し、全主導来対象間のHom比較を全単射にする。 -/
lemma criterionDerivedHom_all (X Y : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  have h := brownHomComparison_all A D E T (𝟙 (T.obj Y)) hcop
    (fun p => by
      change Function.Bijective
        (fun f : moduleCompactGenerators A D p ⟶ Y => T.map f ≫ 𝟙 (T.obj Y))
      simpa only [Category.comp_id] using
        criterionDerivedHom_fromPerfect_all A D E T G hG hcop hperf hhom
          (moduleCompactGenerators A D p)
          (moduleCompact_perfect A D (moduleCompactGenerators_compact A D p)) Y) X
  change Function.Bijective (fun f : X ⟶ Y => T.map f ≫ 𝟙 (T.obj Y)) at h
  simpa only [Category.comp_id] using h

/-- Perf上の充満忠実な比較から、実際の全主導来関手の充満忠実性を得る。 -/
def criterionDerivedFullyFaithful : T.FullyFaithful := by
  let : T.Full := ⟨fun {X Y} => (criterionDerivedHom_all A D E T G hG hcop hperf hhom X Y).2⟩
  let : T.Faithful := ⟨fun {X Y} => (criterionDerivedHom_all A D E T G hG hcop hperf hhom X Y).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful T

end SerrePositivity.DifferentialGraded.Morita
