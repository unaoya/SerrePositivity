module
public import SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.ArrowStableExact

public import SerrePositivity.KST.LocalizingInvariants.LaxInclusionExact
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStability

/-!
概要：安定圏の矢印圏の安定性と、両端による完全性の判定。
方針：恒等二関手の lax pullback との厳密同型で元の F2 の完全射影を輸送する。
規約：元の内部 Hom の全単体を使う。使われ方：cofiber 回転による差の関手の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable (X : SSet.{u})

variable [Quasicategory X] [IsStable X]

lemma arrow_exact_of_endpoints {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    [IsExactFunctor (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))]
    [IsExactFunctor (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))] :
    IsExactFunctor a := by
  let C : StableCategory.{u} := ⟨X, inferInstance, inferInstance⟩
  let p : ExactMap C C := ⟨𝟙 X, inferInstance⟩
  have hf : IsExactFunctor ((a ≫ arrowLaxInverse X) ≫ (laxFst p p).hom) := by
    change IsExactFunctor ((a ≫ arrowLaxInverse X) ≫ F2.laxPullbackFst (𝟙 X) (𝟙 X))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse_fst]
    infer_instance
  have hs : IsExactFunctor ((a ≫ arrowLaxInverse X) ≫ (laxSnd p p).hom) := by
    change IsExactFunctor ((a ≫ arrowLaxInverse X) ≫ F2.laxPullbackSnd (𝟙 X) (𝟙 X))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse_snd]
    infer_instance
  have : IsExactFunctor (a ≫ arrowLaxInverse X) := LaxInclusion.exact_of_components p p _
  have he : IsExactFunctor (F2.laxPullbackArrow (𝟙 X) (𝟙 X)) :=
    inferInstanceAs (IsExactFunctor (arrowLaxIso X).hom)
  have h : IsExactFunctor ((a ≫ arrowLaxInverse X) ≫
      F2.laxPullbackArrow (𝟙 X) (𝟙 X)) := inferInstance
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse_arrow, Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants
