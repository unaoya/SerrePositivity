module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantProduct
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor

/-!
概要：固定底への係数射影を、weighted nerve 全体の同じ底への射に束ねる。
方針：元の係数自然変換を weighted nerve に写し、定値係数の最後の成分で評価する。
規約：係数の Kan 性は要求せず、元のパラメータを保持する。
使われ方：left fibration 値の strict 図式の、積上の共同分類空間。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 元の全係数の固定底への射影を同時に評価する。 -/
def weightedNerveParameter : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantEvaluation I B

/-- 同じ係数射影と同じ添字を持つ、元の積への共同射影。 -/
def weightedNerveParameterProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ B ⊗ nerve I :=
  lift (weightedNerveParameter η) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)

/-- 元の指定単体の底パラメータは、最後の係数の元の射影で計算される。 -/
lemma weightedNerveParameter_yoneda {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ weightedNerveParameter η =
      s.2.app (Fin.last n) ≫ η.app (s.1.obj (Fin.last n)) := by
  rw [SSet.yonedaEquiv_symm_comp]
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (s.2.app (Fin.last n) ≫ η.app (s.1.obj (Fin.last n)))) = _
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- 元の taut scaffold のパラメータは始点の同じ係数射影。 -/
lemma tautScaffold_parameter {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F ≫ weightedNerveParameter η =
      s.2 ≫ η.app (s.1.obj 0) := by
  rcases s with ⟨σ, τ⟩
  rw [← Category.assoc, SSet.yonedaEquiv_symm_comp]
  rw [weightedNerveParameter_yoneda]
  change (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ τ ≫
    F.map (σ.map (homOfLE _))) ≫ η.app _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, η.naturality]
  change τ ≫ η.app (σ.obj 0) ≫ 𝟙 B = τ ≫ η.app (σ.obj 0)
  exact congrArg (fun f ↦ τ ≫ f) (Category.comp_id (η.app (σ.obj 0)))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
