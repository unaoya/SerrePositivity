module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveConstantProduct
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFunctor

/-!
概要：固定底への係数射影を、weighted nerve 全体の同じ底への射に束ねる。
方針：元の係数自然変換を weighted nerve に写し、定値係数の最後の成分で評価する。
規約：係数の Kan 性は要求せず、元のパラメータを保持する。
使われ方：left fibration 値の strict 図式の、積上の共同分類空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 元の全係数の固定底への射影を同時に評価する。 -/
def weightedNerveParameter : weightedNerve F ⟶ B :=
  weightedNerveMap η ≫ weightedNerveConstantEvaluation I B

/-- 同じ係数射影と同じ添字を持つ、元の積への共同射影。 -/
def weightedNerveParameterProjection : weightedNerve F ⟶ B ⊗ nerve I :=
  lift (weightedNerveParameter η) (weightedNerveProjection F)

/-- 元の指定単体の底パラメータは、最後の係数の元の射影で計算される。 -/
lemma weightedNerveParameter_yoneda {n : ℕ} (s : weightedNerveSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ weightedNerveParameter η =
      s.2.app (Fin.last n) ≫ η.app (s.1.obj (Fin.last n)) := by
  rw [SSet.yonedaEquiv_symm_comp]
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (s.2.app (Fin.last n) ≫ η.app (s.1.obj (Fin.last n)))) = _
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- 元の taut scaffold のパラメータは始点の同じ係数射影。 -/
lemma tautScaffold_parameter {n : ℕ} (s : simplicialReplacementSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ tautScaffold F ≫ weightedNerveParameter η =
      s.2 ≫ η.app (s.1.obj 0) := by
  rcases s with ⟨σ, τ⟩
  rw [← Category.assoc, SSet.yonedaEquiv_symm_comp]
  rw [weightedNerveParameter_yoneda]
  change (stdSimplex.map (simplexPrefixInclusion n n _) ≫ τ ≫
    F.map (σ.map (homOfLE _))) ≫ η.app _ = _
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, η.naturality]
  change τ ≫ η.app (σ.obj 0) ≫ 𝟙 B = τ ≫ η.app (σ.obj 0)
  exact congrArg (fun f ↦ τ ≫ f) (Category.comp_id (η.app (σ.obj 0)))

end SerrePositivity.InfinityCategories.F2.Ind
