module
public import SerrePositivity.KST.ProExcision.Conjugation
public import Mathlib.Tactic.FinCases

/-!
# 共役の実区間写像の自然性

概要：Construction A.6 の実ホモトピーが群準同型と可換であることを証明する。
方針：区間圏の三種類の射を調べ、nerve の単体を評価する。
規約：KST Construction A.6 の h↦u⁻¹hu の向き。
使われ方：作用を含む同変ホモトピーの自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory MonoidalCategory SerrePositivity.NerveHomotopy
variable {H H' : Type u} [Group H] [Group H']

/-- 概要：共役の区間関手は群準同型と可換。
方針：区間圏の射 0→0、0→1、1→1 を計算する。
規約：KST Construction A.6。使われ方：nerve の実ホモトピーの自然性。 -/
theorem conjugationInterval_naturality (f : H →* H') (u : H) :
    interval (conjugationNaturalTransformation u) ⋙ SingleObj.mapHom H H' f =
      (Functor.prod (𝟭 (Fin 2)) (SingleObj.mapHom H H' f)) ⋙
        interval (conjugationNaturalTransformation (f u)) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) ?_
  intro x y a
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hij : i ≤ j := leOfHom a.1
  fin_cases i <;> fin_cases j
  · simp [eqToHom_refl, interval, Functor.uncurry, ComposableArrows.mk₁]
  · simp [eqToHom_refl, interval, Functor.uncurry, ComposableArrows.mk₁,
      conjugationNaturalTransformation, conjugationFunctor, inverseConjugation,
      SingleObj.comp_as_mul, map_mul, map_inv]
  · norm_num at hij
  · simp [eqToHom_refl, interval, Functor.uncurry, ComposableArrows.mk₁,
      conjugationNaturalTransformation, conjugationFunctor, inverseConjugation,
      SingleObj.comp_as_mul, SingleObj.id_as_one, map_mul, map_inv]
    rfl

/-- 概要：共役の nerve の実区間写像は群準同型と可換。
方針：区間関手の自然性を各単体に適用する。
規約：KST Construction A.6 の標準ホモトピー。使われ方：同変な線形ホモトピーへの移送。 -/
theorem conjugationNerveHomotopy_naturality (f : H →* H') (u : H) :
    (conjugationNerveHomotopy u).h ≫ nerveMap (SingleObj.mapHom H H' f) =
      (nerveMap (SingleObj.mapHom H H' f) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        (conjugationNerveHomotopy (f u)).h := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change ((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1 ⋙
    interval (conjugationNaturalTransformation u)) ⋙ SingleObj.mapHom H H' f = _
  rw [Functor.assoc, conjugationInterval_naturality f u]
  rfl

/-- 概要：C(H) のテンソル区間ホモトピーは群準同型と可換。
方針：nerve の実区間写像の自然性と自由化のテンソル同型の自然性を合成する。
規約：KST Construction A.6 の非被約な標準ホモトピー。
使われ方：Lemma 4.16 の同変ホモトピーの自然性。 -/
theorem conjugationLinearizedHomotopy_naturality (f : H →* H') (u : H) :
    (conjugationLinearizedHomotopy u).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (SingleObj.mapHom H H' f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (SingleObj.mapHom H H' f)))
        (𝟙 _) ≫ (conjugationLinearizedHomotopy (f u)).h := by
  let F := (SimplicialObject.whiskering _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization
  let p := nerveMap (SingleObj.mapHom H H' f)
  let I := SSet.stdSimplex.obj (SimplexCategory.mk 1)
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (F.map p) (𝟙 _) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso (nerve (SingleObj H')) I).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso (nerve (SingleObj H)) I).hom ≫ F.map (p ▷ I) := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso_naturality p (𝟙 I)
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap, CategoryTheory.Functor.map_id, tensorHom_id] at hh
    exact hh
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso (nerve (SingleObj H)) I).hom ≫
      F.map (conjugationNerveHomotopy u).h) ≫ F.map p =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (F.map p) (𝟙 _) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorIso (nerve (SingleObj H')) I).hom ≫
        F.map (conjugationNerveHomotopy (f u)).h)
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap _ _) _, hn]
  simp only [Category.assoc, ← F.map_comp]
  rw [conjugationNerveHomotopy_naturality f u]

end SerrePositivity.KST.ProExcision
