module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveEmptySieve
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
public import Mathlib.Data.Fintype.EquivFin

/-!
概要：任意の宇宙の有限 cofan の脚は、同じ extensive 位相の被覆篩を生成する。
方針：既存の cofan の再添字の普遍性で Fin n に移し、Mathlib の被覆判定を使う。
  文献対応：HTT 6.2.2.6 の extensive 位相の有限被覆と空被覆。
規約：元の有限 Type u の量化を狭めず、空族も保持する。
使われ方：S1 の元の有限積判定と被覆篩での層条件の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] [FinitaryExtensive C]

/-- 任意の有限 cofan の同じ脚が生成する篩は被覆。
元の Type u の添字を、既存の再添字の同値で Type 0 の有限表示へ運ぶ。 -/
lemma cofanGeneratedSieve_mem_extensiveTopology {ι : Type u} [Finite ι]
    {B : ι → C} (c : Cofan B) (hc : IsColimit c) :
    cofanGeneratedSieve c ∈ (extensiveTopology C) c.pt := by
  classical
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  apply (extensiveTopology.mem_sieves_iff_contains_colimit_cofan _).mpr
  refine ⟨Fin (Fintype.card ι), inferInstance, (fun j => B (e.symm j)),
    (fun j => c.inj (e.symm j)), ⟨?_⟩, ?_⟩
  · exact Cofan.isColimitEquivOfEquiv e.symm c hc
  · intro j
    exact Sieve.ofArrows_mk B c.inj (e.symm j)

/-- 初対象上の空被覆は、同じ extensive 位相に属する。 -/
lemma bottomSieve_mem_extensiveTopology_initial :
    (⊥ : Sieve (⊥_ C)) ∈ (extensiveTopology C) (⊥_ C) := by
  let B : PEmpty.{u + 1} → C := PEmpty.elim
  let c : Cofan B := Cofan.mk (⊥_ C) (fun i => PEmpty.elim i)
  have hc : IsColimit c := Cofan.IsColimit.mk c (fun s => initial.to s.pt)
    (fun s i => PEmpty.elim i) (fun s m hm => initialIsInitial.hom_ext _ _)
  have h := cofanGeneratedSieve_mem_extensiveTopology c hc
  rw [cofanGeneratedSieve_eq_bot] at h
  exact h

/-- 元の extensive 層の初対象での値は、同じ頂点として終対象。 -/
lemma isTerminal_initial_of_isSheaf_extensive {E : SSet.{u + 1}} [Quasicategory E]
    (F : Presheaf C E) (hF : IsSheaf (extensiveTopology C) F) :
    IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C))))) :=
  (restrictionCone_bot_isLimit_iff F (⊥_ C)).mp
    (hF (⊥_ C) ⊥ bottomSieve_mem_extensiveTopology_initial)

end SerrePositivity.InfinityCategories.Sheaves
