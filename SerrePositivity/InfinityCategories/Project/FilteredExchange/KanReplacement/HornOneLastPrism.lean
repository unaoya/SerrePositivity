module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：最後の一次ホーンの積は元の円柱の終点に因子分解する。
方針：ホーンの全単体が一に定値であることを頂点で確認する。
規約：全パラメータ。使われ方：終点固定の境界ホモトピー延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：最後の一次ホーンとの積の包含は時刻一の端点を経由する。
方針：値域から零が欠けることを使う。規約：全単体。使われ方：終点固定の貼り合わせ。 -/
lemma hornOneLast_prism_factorization (A : SSet.{u}) :
    ((horn 1 1).ι ▷ A) = snd (horn 1 1 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range s.val (1 : Fin 2)).1 s.property
    have hj₀ : j = 0 := by
      apply Fin.ext
      change j.val = 0
      have h := j.isLt
      have hn : j.val ≠ 1 := fun h ↦ hj (Fin.ext h)
      omega
    subst j
    have hi : (s.val i).val ≠ 0 := fun h ↦ hm ⟨i, Fin.ext h⟩
    apply Fin.ext
    change (s.val i).val = 1
    have h := (s.val i).isLt
    omega
  · rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
