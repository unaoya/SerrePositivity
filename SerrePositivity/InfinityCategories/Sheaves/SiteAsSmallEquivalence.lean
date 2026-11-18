module

public import SerrePositivity.InfinityCategories.Sheaves.LargeSiteAsSmall

/-!
概要：対象の宇宙が違う二つの site の同値を、同じ AsSmall 表示の site 同値へ移す。
方針：元の圏同値と元の誘導位相の被覆判定を合成し、篩の順像の合成則を用いる。
  文献対応：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の本質的小さい site の模型比較。
規約：元の位相と被覆保存性を保ち、新しい濃度条件は加えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Functor SSet
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type v} [Category.{u} C] {D : Type w} [Category.{u} D]

/-- 対象の宇宙が違う同値を、共通の同じ宇宙の通常圏の同値へ表示する。 -/
def siteAsSmallEquivalence (e : C ≌ D) :
    AsSmall.{max u v w} C ≌ AsSmall.{max u v w} D :=
  (AsSmall.equiv (C := C)).symm.trans (e.trans (AsSmall.equiv (C := D)))

/-- 元の site の被覆保存性は、元の誘導位相を持つ AsSmall 表示へ移る。 -/
lemma siteAsSmallEquivalence_coverPreserving (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hf : CoverPreserving J K e.functor) :
    CoverPreserving
      ((AsSmall.down : AsSmall.{max u v w} C ⥤ C).inducedTopology J)
      ((AsSmall.down : AsSmall.{max u v w} D ⥤ D).inducedTopology K)
      (siteAsSmallEquivalence e).functor := by
  letI : (AsSmall.down : AsSmall.{max u v w} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_inverse
  letI : (AsSmall.down : AsSmall.{max u v w} D ⥤ D).IsEquivalence :=
    (AsSmall.equiv (C := D)).isEquivalence_inverse
  constructor
  intro X S hS
  rw [mem_inducedTopology_iff_of_isCoverDense] at hS ⊢
  rw [← Sieve.functorPushforward_comp]
  change S.functorPushforward
      ((AsSmall.down : AsSmall.{max u v w} C ⥤ C) ⋙ e.functor) ∈
        K (e.functor.obj (AsSmall.down.obj X))
  rw [Sieve.functorPushforward_comp]
  exact hf.cover_preserve hS

end SerrePositivity.InfinityCategories.Sheaves
