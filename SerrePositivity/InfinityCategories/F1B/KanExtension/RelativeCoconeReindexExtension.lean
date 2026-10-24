module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCosliceEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitReindex

/-!
概要：同値な単射上の余錐を、元の図式と像の余錐を固定して延長する。
方針：相対 coslice 制限の自明 Kan 性の切断で指定頂点を持ち上げる。
規約：余錐の像と制限は raw な射の等式として保つ。
使われ方：標準局所相対余極限を comma fiber へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：同値な単射上の余錐は底の指定余錐を保って延長できる。
方針：部分余錐と底の余錐を相対 coslice の引き戻しの頂点にまとめて持ち上げる。
規約：元の図式 p と像の余錐 b を同時に固定する。
使われ方：局所余錐の添字変更における像の厳密な保存。 -/
lemma exists_kanCocone_extension_over_precompositionEquivalence {A K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (i : A ⟶ K) [Mono i] (hi : IsPrecompositionEquivalence i)
    (c : JoinCocone (i ≫ p)) (b : JoinCocone (p ≫ U))
    (hc : c.val ≫ U = joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ b.val) :
    ∃ d : JoinCocone p, (d.restrict i).val = c.val ∧ d.val ≫ U = b.val := by
  have := kanRelativeCosliceRestriction_trivialKanFibration_of_precompositionEquivalence p U hU i hi
  let a : (Δ[0] : SSet.{u}) ⟶ sliceUnder (i ≫ p) := SSet.yonedaEquiv.symm c
  let f : (Δ[0] : SSet.{u}) ⟶ sliceUnder (p ≫ U) := SSet.yonedaEquiv.symm b
  have hcompat : a ≫ sliceUnderPostcomp (i ≫ p) U = f ≫ sliceUnderRestrict (p ≫ U) i := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    congr 1
    exact Subtype.ext hc
  let t := pullback.lift a f hcompat
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (relativeCosliceRestriction p U i)
  let l := t ≫ s
  have hl : l ≫ relativeCosliceRestriction p U i = t := by
    exact (Category.assoc t s (relativeCosliceRestriction p U i)).trans
      ((congrArg (fun r ↦ t ≫ r) hs).trans (Category.comp_id t))
  have hla : l ≫ sliceUnderRestrict p i = a := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst (sliceUnderPostcomp (i ≫ p) U)
      (sliceUnderRestrict (p ≫ U) i)) hl
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc, t,
      pullback.lift_fst] using h
  have hlf : l ≫ sliceUnderPostcomp p U = f := by
    have h := congrArg (fun z ↦ z ≫ pullback.snd (sliceUnderPostcomp (i ≫ p) U)
      (sliceUnderRestrict (p ≫ U) i)) hl
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc, t,
      pullback.lift_snd] using h
  refine ⟨SSet.yonedaEquiv l, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv hla
    rw [SSet.yonedaEquiv_comp] at h
    change (sliceUnderRestrict p i).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv l) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm c) at h
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  · have h := congrArg SSet.yonedaEquiv hlf
    rw [SSet.yonedaEquiv_comp] at h
    change (sliceUnderPostcomp p U).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv l) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm b) at h
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h

/-- 概要：標準の相対余極限余錐も同値な単射に沿って像を固定して延長できる。
方針：余錐を延長し、制限による相対余極限性の保存・反映を適用する。
規約：余錐を独立に選び直さず、指定部分と底の余錐を保つ。
使われ方：局所の相対余極限の存在を comma の局所形へ移す。 -/
lemma exists_kanRelativeColimit_extension_over_precompositionEquivalence
    {A K D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (p : K ⟶ D) (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (i : A ⟶ K) [Mono i] (hi : IsPrecompositionEquivalence i)
    (c : JoinCocone (i ≫ p)) (b : JoinCocone (p ≫ U))
    (hc : c.val ≫ U = joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ b.val)
    (hcol : IsRelativeColimitCone U c) :
    ∃ d : JoinCocone p, IsRelativeColimitCone U d ∧
      (d.restrict i).val = c.val ∧ d.val ≫ U = b.val := by
  obtain ⟨d, hd, hb⟩ := exists_kanCocone_extension_over_precompositionEquivalence p U hU i hi c b hc
  have he : d.restrict i = c := Subtype.ext hd
  refine ⟨d, ?_, hd, hb⟩
  apply (kanIsRelativeColimitCone_iff_restrict_of_precompositionEquivalence U d i hi).2
  rw [he]
  exact hcol

end SerrePositivity.InfinityCategories.F1B
