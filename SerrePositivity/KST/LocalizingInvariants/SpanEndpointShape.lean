module

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanBoundary

/-!
概要：span の二つの終点を初頂点 horn の実部分形状として同時に指定する。
方針：欠ける辺の境界は horn に含まれることを、境界単体の定値性から示す。
規約：形状の包含は単射。使われ方：両端固定 span の内ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def spanEndpointInclusion : (boundary 1 : SSet.{u}) ⟶ (horn 2 0 : SSet.{u}) :=
  Subcomplex.lift ((boundary 1).ι ≫ stdSimplex.δ (0 : Fin 3)) (by
    rintro ⟨⟨n⟩⟩ _ ⟨s, rfl⟩
    rw [mem_horn_iff_notMem_range]
    by_cases hs : s.val 0 = 0
    · refine ⟨2, by decide, ?_⟩
      rintro ⟨j, hj⟩
      change Fin.succ (s.val j) = 2 at hj
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j, hs] at hj
      contradiction
    · have hs' : s.val 0 = 1 := by
        have h := (s.val 0).isLt
        apply Fin.ext
        change (s.val 0).val = 1
        have hn : (s.val 0).val ≠ 0 := fun h => hs (Fin.ext h)
        omega
      refine ⟨1, by decide, ?_⟩
      rintro ⟨j, hj⟩
      change Fin.succ (s.val j) = 1 at hj
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j, hs'] at hj
      contradiction)

lemma spanEndpointInclusion_ι : spanEndpointInclusion.{u} ≫ (horn 2 0).ι =
    (boundary 1).ι ≫ stdSimplex.δ (0 : Fin 3) := rfl

instance spanEndpointInclusion_mono : Mono spanEndpointInclusion.{u} := by
  have : Mono (spanEndpointInclusion.{u} ≫ (horn 2 0).ι) := by
    rw [spanEndpointInclusion_ι]
    infer_instance
  exact mono_of_mono (spanEndpointInclusion.{u}) (horn 2 0).ι

lemma spanEndpointInclusion_app {n : ℕ} (s : (boundary 1 : SSet.{u}) _⦋n⦌) :
    spanEndpointInclusion.app (Opposite.op ⦋n⦌) s =
      if s.val 0 = 0 then horn₂₀.ι₀₁.app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n)
      else horn₂₀.ι₀₂.app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n) := by
  apply Subtype.ext
  split_ifs with hs
  · apply stdSimplex.ext
    intro j
    change Fin.succ (s.val j) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j, hs]
    rfl
  · apply stdSimplex.ext
    intro j
    change Fin.succ (s.val j) = 2
    have hs' : s.val 0 = 1 := by
      have h := (s.val 0).isLt
      have hn : (s.val 0).val ≠ 0 := fun h => hs (Fin.ext h)
      apply Fin.ext
      change (s.val 0).val = 1
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j, hs']
    rfl

lemma markedSpanBoundary_restriction (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    markedSpanBoundary X W = markedSpanInclusion X W ≫ (pre spanEndpointInclusion).app X := by
  apply uncurry_injective
  rw [markedSpanBoundary, uncurry_curry, uncurry_pre_app]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, v⟩
  change (if s.val 0 = 0 then
    v.val.app (Opposite.op ⦋n⦌) (𝟙 _) (horn₂₀.ι₀₁.app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n))
    else v.val.app (Opposite.op ⦋n⦌) (𝟙 _) (horn₂₀.ι₀₂.app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) n))) =
    v.val.app (Opposite.op ⦋n⦌) (𝟙 _) (spanEndpointInclusion.app (Opposite.op ⦋n⦌) s)
  rw [spanEndpointInclusion_app]
  split_ifs <;> rfl

end SerrePositivity.KST.LocalizingInvariants
