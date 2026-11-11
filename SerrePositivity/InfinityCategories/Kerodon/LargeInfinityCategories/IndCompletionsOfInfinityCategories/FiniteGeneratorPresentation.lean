module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
概要：元の単体集合を、有限個の非退化単体で生成される同じ部分複体の余極限として表示する。
方針：生成部分複体の単調な被覆を、部分複体関手の filtered 余極限保存で写す。
規約：元の単体集合への各射は同じ部分複体の包含。
使われ方：κ-small 形状の通常の κ-presentability と相対因子分解。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の有限個の非退化単体が生成する部分複体。 -/
def finiteGeneratorSubcomplex (K : SSet.{u}) (s : Finset K.N) : K.Subcomplex :=
  ⨆ t : s, t.val.subcomplex

instance finiteGeneratorSubcomplex_finite (K : SSet.{u}) (s : Finset K.N) :
    (finiteGeneratorSubcomplex K s).toSSet.Finite := by
  dsimp only [finiteGeneratorSubcomplex]
  apply (SSet.finite_iSup_iff _).mpr
  intro t
  infer_instance

/-- 生成する非退化単体を増やすと、元の部分複体は大きくなる。 -/
lemma finiteGeneratorSubcomplex_monotone (K : SSet.{u}) :
    Monotone (finiteGeneratorSubcomplex K) := by
  intro s t h
  apply iSup_le
  intro z
  exact le_iSup_of_le ⟨z.val, h z.property⟩ le_rfl

/-- 同じ有限生成部分複体は元の単体集合全体を覆う。 -/
lemma iSup_finiteGeneratorSubcomplex (K : SSet.{u}) :
    ⨆ s : Finset K.N, finiteGeneratorSubcomplex K s = ⊤ := by
  classical
  apply le_antisymm le_top
  rw [← N.iSup_subcomplex_eq_top]
  apply iSup_le
  intro t
  exact le_iSup_of_le {t} (le_iSup_of_le ⟨t, Finset.mem_singleton_self t⟩ le_rfl)

/-- 同じ有限生成部分複体の元の包含からなる図式。 -/
def finiteGeneratorDiagram (K : SSet.{u}) : Finset K.N ⥤ SSet.{u} :=
  (finiteGeneratorSubcomplex_monotone K).functor ⋙ Subcomplex.toSSetFunctor

/-- 元の有限生成部分複体の包含を脚とする余錐。 -/
def finiteGeneratorCocone (K : SSet.{u}) : Cocone (finiteGeneratorDiagram K) where
  pt := K
  ι := { app := fun s => (finiteGeneratorSubcomplex K s).ι }

/-- 同じ有限生成部分複体の元の包含の余錐は、通常の単体集合の圏で余極限。 -/
def finiteGeneratorCocone_isColimit (K : SSet.{u}) : IsColimit (finiteGeneratorCocone K) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone (finiteGeneratorSubcomplex_monotone K).functor).isColimit)
    (Cocone.ext (Subcomplex.eqToIso (iSup_finiteGeneratorSubcomplex K) ≪≫ Subcomplex.topIso K))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
