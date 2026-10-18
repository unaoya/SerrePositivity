module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
概要：短完全列の右端を引き戻した短完全列。
方針：元の核の普遍性と pullback の射の一致判定で核を構成する。
規約：任意のアーベル圏での構成。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の非有界準同型拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) {E : C} (p : E ⟶ S.X₃)

/--
概要：短複体の右端を引き戻した短複体。
方針：核の候補は元の第一射と零射の pullback への持ち上げ。
規約：選ばれた実際の pullback を使う。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型拡大の短完全列。
-/
def shortComplexPullback : ShortComplex C :=
  ShortComplex.mk (pullback.lift S.f 0 (by simp)) (pullback.snd S.g p) (by simp)

/--
概要：右端の引き戻しは短完全性を保つ。
方針：第一射の核の普遍性と全射の pullback での保存を使う。
規約：p の単射性・全射性は不要。
使われ方：Stacks Lemma 19.12.5、TT §3・§8 の非有界準同型拡大。
-/
lemma shortComplexPullback_shortExact (hS : S.ShortExact) : (shortComplexPullback S p).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hm : Mono ((shortComplexPullback S p).f ≫ pullback.fst S.g p) := by
    simpa [shortComplexPullback] using (inferInstance : Mono S.f)
  have : Mono (shortComplexPullback S p).f := mono_of_mono _ (pullback.fst S.g p)
  have : Epi (shortComplexPullback S p).g := by
    change Epi (pullback.snd S.g p)
    infer_instance
  apply ShortComplex.ShortExact.mk'
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  have hz : (k ≫ pullback.fst S.g p) ≫ S.g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (k ≫ (shortComplexPullback S p).g) ≫ p = 0
    rw [hk, zero_comp]
  refine ⟨hS.exact.lift (k ≫ pullback.fst S.g p) hz, ?_⟩
  apply pullback.hom_ext
  · simp [shortComplexPullback, Category.assoc]
  · simpa [shortComplexPullback, Category.assoc] using hk.symm
  all_goals infer_instance

end SerrePositivity.KST.DerivedGeometry
