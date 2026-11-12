module

public import SerrePositivity.KST.LocalizingInvariants.CompletionCofiberWide
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberHoDenominators
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：密な完全包含の元の cofiber 分母で、同じ対象への零射を実現する。
方針：指定 retract の包含の fiber 三角形を取り、retract 式でその第一射を零にする。
規約：元の本質像を保ち、辺の h 圏の零性を全図式収縮とは同一視しない。
使われ方：Sp-7 の wide 部分圏の成分収縮と、元の分母による同時均等化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
include h
local instance : HasZeroObject D.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasZeroObject_ho (X := D)
local instance : Preadditive D.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := D)
local instance : HasShift D.HomotopyCategory ℤ :=
  inferInstanceAs (HasShift (hoFunctor.obj D) ℤ)
local instance (n : ℤ) : (shiftFunctor D.HomotopyCategory n).Additive :=
  inferInstanceAs ((shiftFunctor (hoFunctor.obj D) n).Additive)
local instance : Pretriangulated D.HomotopyCategory :=
  inferInstanceAs (Pretriangulated (hoFunctor.obj D))

/-- 概要：各対象へ入る元の分母を、同じ h 圏の零射で選べる。
方針：指定 retract の包含の fiber 三角形を取り、retract 式でその第一射を零にする。
規約：元の本質像を保ち、辺の h 圏の零性を全図式収縮とは同一視しない。
使われ方：Sp-7 の wide 部分圏の成分収縮と、元の分母による同時均等化。 -/
lemma exists_completionNullDenominator (x : D _⦋0⦌) :
    ∃ (z : D _⦋0⦌) (t : Truncated.Edge (X := (truncation 2).obj D) z x),
      t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) ∧
        (Truncated.HomotopyCategory.homMk t :
          (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk x) = 0 := by
  obtain ⟨c, ⟨r⟩⟩ := h.2.2 x
  obtain ⟨z, t, k, ht⟩ := distinguished_cocone_triangle₁ r.i
  have hti : t ≫ r.i = 0 := comp_distTriang_mor_zero₁₂ _ ht
  have htz : t = 0 := by
    calc
      t = t ≫ (r.i ≫ r.r) := by rw [r.retract, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, hti, zero_comp]
  have hw : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (completionEssentialImage f)).trW t :=
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (completionEssentialImage f)).trW_iff_of_distinguished
      (Triangle.mk t r.i k) ht).2 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨c, ⟨Iso.refl _⟩⟩)
  obtain ⟨z, rfl⟩ := Truncated.HomotopyCategory.mk_surjective z
  obtain ⟨t, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z x t
  refine ⟨z, t, ?_, htz⟩
  have he := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_iff_trW (completionEssentialImage f) t).2 hw
  rw [stableClosure_completionEssentialImage f h.2.1] at he
  exact he

/-- 概要：同じ源からの全ての射は、一つの実分母の前合成で同時に零になる。
添字集合の有限性は不要であり、分母は各射に依存しない。
方針：指定 retract の包含の fiber 三角形を取り、retract 式でその第一射を零にする。
規約：元の本質像を保ち、辺の h 圏の零性を全図式収縮とは同一視しない。
使われ方：Sp-7 の wide 部分圏の成分収縮と、元の分母による同時均等化。 -/
lemma exists_completionDenominator_annihilating (x : D _⦋0⦌) :
    ∃ (z : D _⦋0⦌) (t : Truncated.Edge (X := (truncation 2).obj D) z x),
      t.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) ∧
        ∀ (y : hoFunctor.obj D) (a : HomotopyCategory.mk x ⟶ y),
          (Truncated.HomotopyCategory.homMk t :
            (HomotopyCategory.mk z : hoFunctor.obj D) ⟶ HomotopyCategory.mk x) ≫ a = 0 := by
  obtain ⟨z, t, ht, hz⟩ := exists_completionNullDenominator f h x
  refine ⟨z, t, ht, fun y a => ?_⟩
  rw [hz, zero_comp]

end SerrePositivity.KST.LocalizingInvariants
