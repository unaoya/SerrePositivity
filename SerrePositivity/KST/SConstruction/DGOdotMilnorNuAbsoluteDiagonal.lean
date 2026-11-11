module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteTriangle

/-!
概要：同じ絶対提示の元零化面の上下二単体が持つ同じ実対角を回収する。
方針：元の共有面を coherent nerve の元の射データとして読む。
規約：二単体と指定対角を置換しない。使われ方：下三角形の全 Hom の零成分判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元上下二単体の共有対角の一単体は厳密に同じ。
方針：元の四角形の二つの三角形制限の対角面を照合する。
規約：ホモトピー類でなく元一単体の等号。使われ方：同じ対角射データの回収。 -/
lemma dgOdotMilnorNuAbsoluteTriangle_diagonal :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.map (SimplexCategory.δ (1 : Fin 3)).op
      (dgOdotMilnorNuAbsoluteNullTriangle R d h 0) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.map (SimplexCategory.δ (1 : Fin 3)).op
        (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) := by
  let F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
    perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
  have hd : stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 0 =
      stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 1 :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal 0).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal 1).symm
  have he := congrArg (fun k => SSet.yonedaEquiv (k ≫ F)) hd
  have ha₀ := congrArg SSet.yonedaEquiv
    (Category.assoc (stdSimplex.δ (1 : Fin 3)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 0) F)
  have ha₁ := congrArg SSet.yonedaEquiv
    (Category.assoc (stdSimplex.δ (1 : Fin 3)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 1) F)
  have h₀ := stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 0 ≫ F) (1 : Fin 3)
  have h₁ := stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} 1 ≫ F) (1 : Fin 3)
  exact h₀.symm.trans (ha₀.symm.trans (he.trans (ha₁.trans h₁)))

/-- 概要：元対角一単体の射データは同じ元三角形の対角 path の像。
方針：元の面制限と豊穣関手の通常射回収の単位評価を使う。
規約：始域・終域・通常射を依存和で同時に保持。使われ方：上下の終関手性の輸送。 -/
lemma dgOdotMilnorNuAbsoluteTriangle_diagonal_data (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.map (SimplexCategory.δ (1 : Fin 3)).op
        (dgOdotMilnorNuAbsoluteNullTriangle R d h j)) =
      (⟨(dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (0 : Fin 3)⟩,
        (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (2 : Fin 3)⟩,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (dgOdotMilnorNuAbsoluteNullTriangle R d h j)).map
          dgOdotMilnorNuNullDiagonalPath.{u}⟩ : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (dgOdotMilnorNuAbsoluteNullTriangle R d h j)
    dgOdotMilnorNuNullDiagonalPath.{u}
  have he := (congrArg (SimplicialCategory.homEquiv' _ _).symm hv.symm).trans
    (Equiv.symm_apply_apply _ _)
  exact congrArg (fun f => (⟨_, _, f⟩ : Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y)) he

end SerrePositivity.KST.SConstruction
