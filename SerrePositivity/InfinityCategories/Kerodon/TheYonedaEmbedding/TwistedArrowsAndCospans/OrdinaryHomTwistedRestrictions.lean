module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedSimplex

/-!
概要：Hom の twisted arrow 比較は、元の左右の全射列を保持する。
方針：重みの左右への制限を既存の包含の法則で計算し、右射影を全次数で照合する。
規約：頂点だけの照合や存在だけの比較ではなく、指定した射の等式を保つ。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の全 Hom 図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 指定重み比較の左制限は元の左の添字比較と指定包含の合成。
Kerodon Proposition 8.1.1.10（Tag 03JN）、模型比較の左制限の法則。 -/
lemma homChainJoinWeight_inl (n : ℕ) :
    joinInl (stdSimplex.obj ⦋n⦌).op (stdSimplex.obj ⦋n⦌) ≫ homChainJoinWeight.{u} n =
      homChainLeftWeight.{u} n ≫ nerveMap.{u, u} (CategoryTheory.Join.inclLeft
        (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1)))) := by
  unfold homChainJoinWeight
  rw [← Category.assoc, joinInl_joinMap, Category.assoc, joinInl_nerveJoinComparison]

/-- 指定重み比較の右制限は標準単体の同型と指定包含の合成。
Kerodon Proposition 8.1.1.10（Tag 03JN）、模型比較の右制限の法則。 -/
lemma homChainJoinWeight_inr (n : ℕ) :
    joinInr (stdSimplex.obj ⦋n⦌).op (stdSimplex.obj ⦋n⦌) ≫ homChainJoinWeight.{u} n =
      (stdSimplex.isoNerve.{u} n).hom ≫ nerveMap.{u, u} (CategoryTheory.Join.inclRight
        (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1)))) := by
  unfold homChainJoinWeight
  rw [← Category.assoc, joinInr_joinMap, Category.assoc, joinInr_nerveJoinComparison]

/-- 指定単体の左制限は元の源の全射列である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、比較射の左制限の法則。 -/
lemma ordinaryHomTwistedSimplex_inl (s : ComposableArrows (OrdinaryHomElements C) n) :
    joinInl (stdSimplex.obj ⦋n⦌).op (stdSimplex.obj ⦋n⦌) ≫ ordinaryHomTwistedSimplex s =
      homChainLeftWeight.{u} n ≫
        nerveMap.{u, u} ((homChainIndexDown n).op ⋙ ordinaryHomSourceChain s) := by
  unfold ordinaryHomTwistedSimplex
  rw [← Category.assoc, homChainJoinWeight_inl, Category.assoc]
  have hn : nerveMap.{u, u} (CategoryTheory.Join.inclLeft (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1)))) ≫
      nerveMap.{u, u} (ordinaryHomLiftedJoinChain s) =
      nerveMap.{u, u} ((homChainIndexDown n).op ⋙ ordinaryHomSourceChain s) := rfl
  rw [hn]

/-- 指定単体の右制限は元の標的の全射列である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、比較射の右制限の法則。 -/
lemma ordinaryHomTwistedSimplex_inr (s : ComposableArrows (OrdinaryHomElements C) n) :
    joinInr (stdSimplex.obj ⦋n⦌).op (stdSimplex.obj ⦋n⦌) ≫ ordinaryHomTwistedSimplex s =
      (stdSimplex.isoNerve.{u} n).hom ≫
        nerveMap.{u, u} (homChainIndexDown n ⋙ ordinaryHomTargetChain s) := by
  unfold ordinaryHomTwistedSimplex
  rw [← Category.assoc, homChainJoinWeight_inr, Category.assoc]
  have hn : nerveMap.{u, u} (CategoryTheory.Join.inclRight (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1)))) ≫
      nerveMap.{u, u} (ordinaryHomLiftedJoinChain s) =
      nerveMap.{u, u} (homChainIndexDown n ⋙ ordinaryHomTargetChain s) := rfl
  rw [hn]

/-- 標準単体の同型から元の射列を評価すると、元の全射列に戻る。
Kerodon Proposition 8.1.1.10（Tag 03JN）、添字の宇宙移送の逆関係。 -/
lemma homChainRightEvaluation (F : Fin (n + 1) ⥤ C) :
    SSet.yonedaEquiv ((stdSimplex.isoNerve.{u} n).hom ≫
      nerveMap.{u, u} (homChainIndexDown n ⋙ F)) = F := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro i j h
  rfl

/-- twisted arrow 比較の右射影は、元の Hom の元の圏の標的射影の nerve そのものである。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ両端射影を保つ比較の右側。 -/
lemma ordinaryHomTwistedComparison_right :
    ordinaryHomTwistedComparison C ≫ edgewiseRight (nerve C) =
      nerveMap.{u, u} (ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.snd Cᵒᵖ C) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInr _ _ ≫ ordinaryHomTwistedSimplex s) = _
  rw [ordinaryHomTwistedSimplex_inr]
  exact homChainRightEvaluation (ordinaryHomTargetChain s)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
