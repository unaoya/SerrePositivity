module

public import SerrePositivity.InfinityCategories.F1B.KanLeftTransportHom
public import SerrePositivity.InfinityCategories.F1B.FunctorHomEvaluationNaturality

/-!
概要：底上の図式間の二胞体が誘導する標準左 Kan 余錐間の射。
方針：slice の普遍余錐で前合成し、図式への制限と頂点評価を計算する。
規約：指定された二胞体の類を保つ。
使われ方：局所普遍余錐の比較から大域的な比較射の各点での可逆性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準左 Kan 余錐を与える底 C への普遍余錐の射。
方針：slice の普遍な余錐を局所添字へ引き戻す。
規約：標的の図式を後合成する前の射を保持する。
使われ方：図式間の二胞体の局所余錐への作用。 -/
def kanLeftCanonicalCoconeMap {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    join (leftKanShape δ c) (Δ[0] : SSet.{u}) ⟶ C :=
  sliceOverUncurry (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c)))

/-- 概要：図式間の射が標準左 Kan 余錐間に誘導する射。
方針：普遍余錐の射に沿う前合成を h Fun に適用する。
規約：元の η を別の射へ置き換えない。
使われ方：比較正方形の標準余錐間の辺。 -/
def kanLeftCanonicalHom {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    {F G : C ⟶ D} (η : FunctorHom F G) :
    FunctorHom (leftKanCanonicalCocone δ F c).val (leftKanCanonicalCocone δ G c).val :=
  (hoFunctor.map ((pre (kanLeftCanonicalCoconeMap δ c)).app D)).toFunctor.map η

/-- 概要：標準余錐間の射の制限は δ と局所添字による元の射の制限。
方針：普遍余錐の図式への制限を計算し、前合成の合成の等式を使う。
規約：両端の図式の同一視を eqToHom で明示する。
使われ方：局所比較正方形の底の可換性。 -/
lemma kanLeftCanonicalHom_restriction {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    {F G : C ⟶ D} (η : FunctorHom F G) :
    (hoFunctor.map (coconeRestriction (leftKanShape δ c) D)).toFunctor.map
        (kanLeftCanonicalHom δ c η) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
          (leftKanCanonicalCocone δ F c).property) ≫
        (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor.map
          ((hoFunctor.map ((pre δ).app D)).toFunctor.map η) ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
          (leftKanCanonicalCocone δ G c).property).symm := by
  have hr : joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ kanLeftCanonicalCoconeMap δ c =
      leftKanProjection δ c ≫ δ := by
    rw [kanLeftCanonicalCoconeMap, sliceOverUncurry_projection, ← pullback.condition]
  have hp : (hoFunctor.map ((pre (kanLeftCanonicalCoconeMap δ c)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}))).app D)).toFunctor =
        (hoFunctor.map ((pre δ).app D)).toFunctor ⋙
          (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, hr, pre_map, NatTrans.comp_app,
      CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor]
  exact CategoryTheory.Functor.congr_hom hp η

/-- 概要：標準余錐間の射が頂点で可逆なら元の二胞体の c 成分も可逆。
方針：普遍余錐の頂点が c に写ることと二胞体の前合成・評価の可換性を使う。
規約：標的 D のみ quasicategory とする。
使われ方：局所比較の可逆性を大域的な二胞体の各点へ戻す。 -/
lemma kanLeftCanonicalHom_component_isIso {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (c : C _⦋0⦌) {F G : C ⟶ D} (η : FunctorHom F G)
    (hη : IsIso ((hoFunctor.map (coconeApexEvaluation (leftKanShape δ c) D)).toFunctor.map
      (kanLeftCanonicalHom δ c η))) : IsIso (functorHomEvaluate η c) := by
  let v := (joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  have hv : (kanLeftCanonicalCoconeMap δ c).app (Opposite.op ⦋0⦌) v = c := by
    have hpoint : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      omega
    dsimp only [v]
    rw [hpoint, ← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp, Category.id_comp]
    rw [kanLeftCanonicalCoconeMap, sliceOverUncurry_fixed, Equiv.apply_symm_apply]
  have he : IsIso (functorHomEvaluate (kanLeftCanonicalHom δ c η) v) := by
    have := hη
    unfold functorHomEvaluate
    change IsIso (eqToHom _ ≫
      (hoFunctor.map (coconeApexEvaluation (leftKanShape δ c) D)).toFunctor.map
        (kanLeftCanonicalHom δ c η) ≫ eqToHom _)
    infer_instance
  have hh := functorHomEvaluate_precomp η (kanLeftCanonicalCoconeMap δ c) v
  have hi : IsIso (functorHomEvaluate η ((kanLeftCanonicalCoconeMap δ c).app _ v)) := hh ▸ he
  exact hv ▸ hi

end SerrePositivity.InfinityCategories.F1B
