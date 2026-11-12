module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionDiagonalMixed
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderHomNormalization

/-!
概要：同じ時刻切断の coherent 合成図式は、豊穣合成の標準区間図式そのもの。
方針：対象と零・混合・一時刻の Hom の一致を豊穣関手の外延性で束ねる。
規約：元の二つの Hom の全単体を保つ。
使われ方：合成三角形全体の対角作用を後合成へ厳密に接続する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 同じ対角の切断単体は、元の豊穣合成の標準区間比較の切断単体と一致する。 -/
lemma coherentCompositionDiagonalCutSimplex_eq
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex σ τ t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) t := by
  let υ := (eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)
  have ho (i : Fin (n + 1)) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex σ τ t).obj ⟨ULift.up i⟩ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex υ t).obj ⟨ULift.up i⟩ := by
    by_cases hi : t i = 0
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero υ t i hi).symm
    · have hi' : t i = 1 := by omega
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_one σ τ t i hi').trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one υ t i hi').symm
  apply EnrichedFunctor.ext SSet (fun i ↦ ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_zero σ τ t j hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero υ t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero υ t j hj)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_zeroHom σ τ t i j hi hj).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_zeroHom υ t i j hi hj).symm
  · have hj' : t j = 1 := by omega
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_one σ τ t j hj')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero υ t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one υ t j hj')
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_mixedHom σ τ t i j hi hj'
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (show Path (ULift.up i : ULift.{u} (Fin (n + 1)))
      (ULift.up j) from P.obj 0)
    have ht := t.monotone hp
    rw [hj] at ht
    exact False.elim (hi (le_antisymm ht (Fin.zero_le _)))
  · have hi' : t i = 1 := by omega
    have hj' : t j = 1 := by omega
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_eq_of_normalized _ _ (ho i) (ho j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_one σ τ t i hi')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_obj_one σ τ t j hj')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one υ t i hi')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one υ t j hj')
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionDiagonalCutSimplex_oneHom σ τ t i j hi' hj').trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_oneHom υ t i j hi' hj').symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
