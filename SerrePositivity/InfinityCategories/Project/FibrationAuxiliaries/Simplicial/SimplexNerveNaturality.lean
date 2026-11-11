module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplexNerveOver

/-!
概要：標準単体の任意の射を有限鎖の関手へ移し、元の単体の制限を保持する。
方針：nerve の充満性で関手を取り、忠実性で底の関手の合成を同定する。
規約：面・退化を含む元の単体写像を使う。
使われ方：標準セル比較を共有面へ制限する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- nerve 写像の等式は、元の通常関手の等式を反映する。 -/
lemma functor_eq_of_nerveMap_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (h : nerveMap F = nerveMap G) : F = G := by
  have hh := congrArg (fun t ↦ nerve.functorOfNerveMap ((SSet.truncation 2).map t)) h
  exact (nerve.functorOfNerveMap_nerveFunctor₂_map F).symm.trans
    (hh.trans (nerve.functorOfNerveMap_nerveFunctor₂_map G))

variable {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])

/-- 元の標準単体の射を表す、同じ有限鎖の関手。 -/
def simplexNerveMapFunctor : ULift.{u} (Fin (m + 1)) ⥤ ULift.{u} (Fin (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor (f ≫ (stdSimplex.isoNerve n).hom)

/-- 同じ有限鎖の関手は元の標準単体の射をそのまま回収する。 -/
lemma simplexNerveMapFunctor_nerveMap :
    nerveMap (simplexNerveMapFunctor f) =
      (stdSimplex.isoNerve m).inv ≫ f ≫ (stdSimplex.isoNerve n).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor_nerveMap _

/-- 標準単体の制限を有限鎖に移すと、底の関手の合成に厳密に一致する。 -/
lemma simplexNerveBaseFunctor_comp {C : Type u} [Category.{u} C]
    (σ : (Δ[n] : SSet.{u}) ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor (f ≫ σ) = simplexNerveMapFunctor f ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ := by
  apply functor_eq_of_nerveMap_eq
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor (f ≫ σ)) =
    nerveMap (simplexNerveMapFunctor f) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor σ)
  rw [simplexNerveMapFunctor_nerveMap,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor_nerveMap, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplexNerveBaseFunctor_nerveMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
