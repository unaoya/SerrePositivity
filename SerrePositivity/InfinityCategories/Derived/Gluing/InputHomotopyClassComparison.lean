module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputRelativeComparison
public import SerrePositivity.InfinityCategories.Core.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-! # 入力固定変形の選択と関手圏の辺の類

概要：同じ入力を保つ二変形は、全パラメーター関手圏の辺として同じ類を持つ。
方針：入力射影の内部 Hom が実自明 Kan fibration であることから忠実性を使う。
規約：単なる端点一致でなく全時間の基底像の一致を要求する。
使われ方：実相対二次元比較を選択済みの二変形へ移す際の合成判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped Simplicial

lemma dgGluingInputHomotopy_homMk_eq {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    {f g : A ⟶ E} (H G : SSet.Homotopy f g) (h : H.h ≫ p = G.h ≫ p) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy G) := by
  have hf := isFullyFaithful_of_trivialKanFibration ((ihom A).map p)
  apply (hf.homotopyCategoryMap_bijective (functorVertex f) (functorVertex g)).1
  change SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((ihom A).map p))) =
    SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy G).map ((truncation 2).map ((ihom A).map p)))
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  change ((ihom A).map p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    ((ihom A).map p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry G.h))
  apply (SSet.yonedaEquiv (X := (ihom A).obj B) (n := ⦋1⦌)).symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply,
    ← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply,
    ← curry_natural_right, ← curry_natural_right, h]

lemma dgGluingFunctorHomotopyPostcomp_edge {A E Z : SSet.{u}}
    {f g : A ⟶ E} (H : SSet.Homotopy f g) (q : E ⟶ Z) :
    (functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((ihom A).map q)) =
      functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H q) := by
  apply SSet.Truncated.Edge.ext
  change ((ihom A).map q).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    SSet.yonedaEquiv (curry (H.h ≫ q))
  apply (SSet.yonedaEquiv (X := (ihom A).obj Z) (n := ⦋1⦌)).symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, curry_natural_right]

lemma dgGluingInputHomotopy_post_homMk_eq {A E B Z : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    {f g : A ⟶ E} (H G : SSet.Homotopy f g) (h : H.h ≫ p = G.h ≫ p) (q : E ⟶ Z) :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H q)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp G q)) := by
  have he := congrArg ((hoFunctor.map ((ihom A).map q)).toFunctor.map)
    (dgGluingInputHomotopy_homMk_eq p H G h)
  change SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((ihom A).map q))) =
    SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy G).map ((truncation 2).map ((ihom A).map q))) at he
  simpa only [dgGluingFunctorHomotopyPostcomp_edge] using he

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

lemma dgGluingLaxHomFirstInputHomotopy_class_independent
    (H : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingLaxHomFirstInputHomotopy R C D M X Y)) := by
  let := dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  let : KanComplex (dgGluingDerivedFirstCompositionInputFiber R C D M X Y) :=
    dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  exact dgGluingInputHomotopy_homMk_eq
    (E := dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
    (dgGluingDerivedFirstCompositionInputProjection R C D M X Y) H _ hH

lemma dgGluingLaxHomLastInputHomotopy_class_independent
    (H : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedLastCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingLaxHomLastInputHomotopy R C D M X Y)) := by
  let := dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  let : KanComplex (dgGluingDerivedLastCompositionInputFiber R C D M X Y) :=
    dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  exact dgGluingInputHomotopy_homMk_eq
    (E := dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (dgGluingDerivedLastCompositionInputProjection R C D M X Y) H _ hH

end SerrePositivity.InfinityCategories
