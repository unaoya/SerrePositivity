module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeCospanSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex

/-!
概要：二辺上の切断を共通終点で貼る表示の、終点制限の Kan fibration 性。
方針：底上の単射制限を通常の相対前合成へ戻し、既存の全ホーン持ち上げを使う。
規約：元の射影の left fibration 性だけを要求。使われ方：切断の厳密な引き戻しの極限性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底上の単射制限による相対前合成は、全 Kan ホーンを持ち上げる。 -/
lemma relativeFunctorOverPre_fibration_of_mono {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] {a b : Over B} (f : a ⟶ b) [Mono f.left] :
    Fibration (relativeFunctorOverPre p f) := by
  obtain ⟨A, a, rfl⟩ := Over.mk_surjective a
  obtain ⟨D, b, rfl⟩ := Over.mk_surjective b
  obtain ⟨i, h, rfl⟩ := Over.homMk_surjective f
  change A ⟶ D at i
  have hi : Mono i := by assumption
  change i ≫ b = a at h
  subst a
  exact relativeFunctorPre_fibration p b i

variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (d : (horn 2 2 : SSet.{u}) ⟶ B)

/-- 左辺の共通終点への実際の制限は Kan fibration。 -/
lemma relativeCospanLeftTarget_fibration :
    Fibration (relativeFunctorOverPre p (relativeCospanLeftTarget d)) := by
  have : Mono (relativeCospanLeftTarget d).left :=
    inferInstanceAs (Mono (stdSimplex.δ (0 : Fin 2)))
  exact relativeFunctorOverPre_fibration_of_mono p _

/-- 右辺の共通終点への実際の制限も Kan fibration。 -/
lemma relativeCospanRightTarget_fibration :
    Fibration (relativeFunctorOverPre p (relativeCospanRightTarget d)) := by
  have : Mono (relativeCospanRightTarget d).left :=
    inferInstanceAs (Mono (stdSimplex.δ (0 : Fin 2)))
  exact relativeFunctorOverPre_fibration_of_mono p _

/-- 各辺の始点への実際の制限は trivial Kan fibration。 -/
lemma relativeCospanEdgeSource_trivialKanFibration (e : (Δ[1] : SSet.{u}) ⟶ B) :
    TrivialKanFibration (relativeFunctorPre p e (stdSimplex.δ (1 : Fin 2))) := by
  apply relativeFunctorPre_trivialKanFibration p e _
  have hv : scaffoldFirstVertex.{u} 1 = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro k
    fin_cases k
    rfl
  rw [← hv]
  exact scaffoldFirstVertex_leftAnodyne 1

end SerrePositivity.InfinityCategories.F2
