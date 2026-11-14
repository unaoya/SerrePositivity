module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

/-!
概要：元の pullback 錐を穿孔 core へ延長し、外側の錐と実比較辺を作る。
方針：同じ native 錐の厳密な制限と頂点を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ と合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreCospanOuterIndexMap :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u} where
  toFun p := by
    have hp := p.property
    have h0 := p.val.property
    change p.val.val.val.val.down.val.1.val ≤ 1 ∧
      p.val.val.val.val.down.val.2.val ≤ 1 at hp
    change 1 ≤ p.val.val.val.val.down.val.1.val +
      p.val.val.val.val.down.val.2.val at h0
    let x : Fin 3 := ⟨2 * p.val.val.val.val.down.val.1.val, by omega⟩
    let y : Fin 3 := ⟨2 * p.val.val.val.val.down.val.2.val, by omega⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint x y, by
      change 1 ≤ 2 * p.val.val.val.val.down.val.1.val +
        2 * p.val.val.val.val.down.val.2.val
      omega⟩
  monotone' := by
    intro p q h
    exact ⟨Nat.mul_le_mul_left 2 h.1, Nat.mul_le_mul_left 2 h.2⟩

def excisionCoreOuterCospanBoundary : (horn 2 2 : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso.hom ≫ nerveMap excisionCoreCospanOuterIndexMap.toFunctor

lemma excisionCoreOuterCospanBoundary_projection :
    excisionCoreOuterCospanBoundary.{u} ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram 1 1 := by
  apply horn₂₂.isPushout.hom_ext
  · simp only [excisionCoreOuterCospanBoundary, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_first,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide
  · simp only [excisionCoreOuterCospanBoundary, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanHornIso,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_second,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;>
      apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
