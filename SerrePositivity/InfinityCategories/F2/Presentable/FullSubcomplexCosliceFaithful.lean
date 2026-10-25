module

public import SerrePositivity.InfinityCategories.F2.Compact.FullCoslicePullback
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting

/-!
概要：全部分複体への図式上の coslice の全比較は充満忠実。
方針：元の coslice の実引き戻し表示と全部分包含の充満忠実性を使う。
規約：頂点条件の同型不変性を明示し、元の全図式を保つ。
使われ方：compact 始域 slice の全余錐同型を周囲の圏から戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：同型不変な全部分複体内の図式の全 coslice 比較は充満忠実。
方針：厳密な引き戻しの比較同型の第二射影へ充満忠実性を移す。
規約：図式の形状に有限性や小ささを要求しない。
使われ方：compact 余錐の全同型の反映と回収。 -/
lemma fullSubcomplex_coslicePostcomp_isFullyFaithful
    {K X : SSet.{u}} [Quasicategory X] (P : X _⦋0⦌ → Prop)
    (hP : ∀ {v w}, VertexIso v w → (P v ↔ P w))
    (a : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    IsFullyFaithful (sliceUnderPostcomp a (fullSubcomplexOnVertices X P).ι) := by
  let j := (fullSubcomplexOnVertices X P).ι
  have : InnerFibration j := F1B.EquivalenceLifting.innerFibration
    (kanEquivalenceLifting_fullSubcomplexOnVertices_ι P hP)
  let h := Compact.fullSliceUnder_isPullback P a
  have : InnerFibration (pullback.snd j (sliceUnderProjection (a ≫ j))) :=
    ⟨innerFibrations.pullback_snd j _ InnerFibration.mem⟩
  have : Quasicategory (pullback j (sliceUnderProjection (a ≫ j))) :=
    quasicategory_of_innerFibration (pullback.snd j (sliceUnderProjection (a ≫ j)))
  have he := (qCatEquivalenceOfIso h.isoPullback).isFullyFaithful.comp
    ((isFullyFaithful_fullSubcomplexOnVertices_ι X P).pullback_snd
      (sliceUnderProjection (a ≫ j)))
  exact (congrArg (fun f ↦ IsFullyFaithful f) h.isoPullback_hom_snd).mp he

end SerrePositivity.InfinityCategories.F2.Presentable
