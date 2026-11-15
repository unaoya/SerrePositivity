module

public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSieveConeComparison
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
概要：元の小さい site と同じ AsSmall 表示で、すべての被覆篩の層条件を比較する。
方針：元の指定制限錐の比較と、Mathlib の誘導位相の被覆の判定を使う。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02K2）の小さい模型に沿う層条件の輸送。
規約：係数は SSet(u+1) のまま、層条件そのものを入力しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 対応する元の被覆篩から、同じ宇宙の二つの指定層条件を保存し反映する。 -/
theorem isSheaf_asSmall_iff (J : GrothendieckTopology C)
    (K : GrothendieckTopology (AsSmall.{u + 1} C))
    (hcov : ∀ (U : C) (S : Sieve (AsSmall.up.obj U)),
      S ∈ K (AsSmall.up.obj U) ↔ S.functorPullback AsSmall.up ∈ J U)
    (O : nerve (AsSmall.{u + 1} C)ᵒᵖ ⟶ E) :
    IsSheaf J ((asSmallSiteShapeIso C).hom ≫ O) ↔ NativeIsSheaf K O := by
  constructor
  · intro h U S hS
    rcases U with ⟨U⟩
    exact (isLimit_asSmallRestrictionCone_iff S O).mp
      (h U _ ((hcov U S).mp hS))
  · intro h U S hS
    letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
      (AsSmall.equiv (C := C)).isEquivalence_functor
    let T := S.functorPushforward (AsSmall.up : C ⥤ AsSmall.{u + 1} C)
    have he : T.functorPullback AsSmall.up = S :=
      Sieve.functorPullback_functorPushforward_eq AsSmall.up
    have hT : T ∈ K (AsSmall.up.obj U) := (hcov U T).mpr (he.symm ▸ hS)
    have hc := (isLimit_asSmallRestrictionCone_iff T O).mpr (h _ T hT)
    rw [he] at hc
    exact hc

/-- AsSmall の逆に沿う篩の順像は、同じ順射に沿う元の篩の逆像と一致する。 -/
lemma asSmall_functorPushforward_down {U : C}
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    S.functorPushforward AsSmall.down = S.functorPullback AsSmall.up := by
  let e : C ≌ AsSmall.{u + 1} C := AsSmall.equiv
  have h := Sieve.functorPushforward_inverse S e
  change S.functorPushforward AsSmall.down =
    (S.pullback (𝟙 (AsSmall.up.obj U))).functorPullback AsSmall.up at h
  simpa only [Sieve.pullback_id] using h

/-- 元の位相を同じ AsSmall 表示へ誘導した場合の、追加条件なしの層条件の同値。 -/
theorem isSheaf_asSmall_inducedTopology_iff (J : GrothendieckTopology C)
    (O : nerve (AsSmall.{u + 1} C)ᵒᵖ ⟶ E) :
    IsSheaf J ((asSmallSiteShapeIso C).hom ≫ O) ↔
      NativeIsSheaf ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J) O := by
  letI : (AsSmall.down : AsSmall.{u + 1} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_inverse
  apply isSheaf_asSmall_iff
  intro U S
  rw [mem_inducedTopology_iff_of_isCoverDense, asSmall_functorPushforward_down]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
