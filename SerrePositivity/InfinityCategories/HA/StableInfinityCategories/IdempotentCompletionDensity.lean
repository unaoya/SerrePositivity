module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RetractComplementCofiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
/-!
概要：完全な冪等完備化射の本質像は、各対象 d とその一回懸垂の双積を含む。
方針：像の retract の補射影を充満忠実性で始域へ戻し、完全性でその cofiber を写す。
規約：元の指定射を使い、S 構成や模型圏の仮定を追加しない。
使われ方：K-cof の一般共終性で、同じ完備化射の本質像を検査する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated SSet
open scoped _root_.Simplicial
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]

/-- 完全な冪等完備化射の本質像は、任意の d ⊕ Σd を含む。 -/
theorem IsExactFunctor.biprod_shift_mem_essentialImage_of_idempotentCompletion
    (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (d : hoFunctor.obj D) :
    ∃ c : hoFunctor.obj C,
      Nonempty (biprod d ((shiftFunctor (hoFunctor.obj D) (1 : ℤ)).obj d) ≅
        (hoFunctor.map f).toFunctor.obj c) := by
  let F := (hoFunctor.map f).toFunctor
  let : F.Full := hf.2.1.toHoFullyFaithful.full
  obtain ⟨d, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective d
  obtain ⟨c, ⟨s⟩⟩ := hf.2.2 d
  let c₀ : hoFunctor.obj C := HomotopyCategory.mk c
  let q : F.obj c₀ ⟶ F.obj c₀ :=
    Sub.sub (α := F.obj c₀ ⟶ F.obj c₀) (𝟙 _) (s.r ≫ s.i)
  let q' : c₀ ⟶ c₀ := F.preimage q
  have hq : F.map q' = q := F.map_preimage (X := c₀) (Y := c₀) q
  obtain ⟨z, g, h, ht⟩ := distinguished_cocone_triangle q'
  have hm := F.map_distinguished (Triangle.mk q' g h) ht
  change Triangle.mk (F.map q') (F.map g)
    (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app (HomotopyCategory.mk c)) ∈
      distTriang (hoFunctor.obj D) at hm
  rw [hq] at hm
  exact ⟨z, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.retractComplementCofiber_biprodShift s.i s.r s.retract
    (F.map g) (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app (HomotopyCategory.mk c)) hm⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExactFunctor (biprod_shift_mem_essentialImage_of_idempotentCompletion)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
