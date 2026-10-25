module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.F2.Presentable.CoYonedaFullyFaithful
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PinchedHomIso
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanOppositeEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.F1.Universe.FunctorSpaceVertex
public import SerrePositivity.InfinityCategories.F1.Universe.PinchedHom

/-!
概要：全 Hom 係数図式間の写像空間を元の反対図式間の写像空間と比較する。
方針：全 co-Yoneda の充満忠実な後合成と内部 Hom の変数交換を合成する。
規約：元の F・G とその係数図式を保持し、A の quasicategory 性を要求しない。
使われ方：P-12 の Yoneda 模型と元の関手圏の Hom との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の co-Yoneda 合成図式の転置は元の Hom 係数前層族そのもの。
方針：既存の係数図式の転置の式と対称性の往復を使う。
規約：全図式の厳密な等式。使われ方：写像空間比較の両頂点の正規化。 -/
lemma coyonedaComposite_transpose {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) :
    curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj A.op)
        ((SSet.uliftFunctor.{u + 1, u}).obj C)).hom ≫
      uncurry ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
        coyonedaInfinityMap C)) = presheafHomWeightDiagram F := by
  rw [← presheafHomWeightDiagram_transpose, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

/-- 概要：元の反対図式間の全自然変換空間と全 Hom 係数図式間の空間は同値。
方針：co-Yoneda の充満忠実な後合成後に二重内部 Hom の交換同型を適用する。
規約：反対図式は元の F・G を宇宙変更したもの。
使われ方：元の Fun の Hom と Yoneda 模型の比較の co-Yoneda 側。 -/
def homWeightDiagramHomEquivalence {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence
      (pinchedHom
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map G)))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F))))
      (pinchedHom (functorVertex (presheafHomWeightDiagram G))
        (functorVertex (presheafHomWeightDiagram F))) := by
  let f := (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F)
  let g := (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map G)
  let e := (((coyonedaInfinityMap_isFullyFaithful C).postcompose
    ((SSet.uliftFunctor.{u + 1, u}).obj A.op))
      (functorVertex g) (functorVertex f)).isQCatEquivalence.choose
  let i := internalHomSwapIso ((SSet.uliftFunctor.{u + 1, u}).obj A.op)
    ((SSet.uliftFunctor.{u + 1, u}).obj C) SpaceInfinity.{u}
  have h : QCatEquivalence (pinchedHom (functorVertex g) (functorVertex f))
      (pinchedHom (functorVertex (g ≫ coyonedaInfinityMap C))
        (functorVertex (f ≫ coyonedaInfinityMap C))) := e
  let q := h.trans (qCatEquivalenceOfIso
    (pinchedHomIsoOfIso i (functorVertex (g ≫ coyonedaInfinityMap C))
      (functorVertex (f ≫ coyonedaInfinityMap C))))
  simpa only [i, internalHomSwapIso_functorVertex, f, g, coyonedaComposite_transpose] using q

/-- 概要：元の関手圏の Hom は、反対図式間の逆向き Hom と同値。
方針：左右の pinched 模型を反転し、内部 Hom の反転同型を適用する。
規約：同値の選択を含み、F・G での自然性は別工程。
使われ方：Hom 係数図式間の写像空間から元の Hom への回収。 -/
def functorHomOppositeEquivalence {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence (pinchedHom (functorVertex F) (functorVertex G))
      (pinchedHom (functorVertex (SSet.opFunctor.map G))
        (functorVertex (SSet.opFunctor.map F))) := by
  let x := functorVertex F
  let y := functorVertex G
  let e := (pinchedHomLeftRightEquivalence x y).symm.trans
    (kanOppositeEquivalence (pinchedHom (X := ((ihom A).obj C).op)
      (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)))
  let i := oppositeInternalHomIso A C
  let h := e.trans (qCatEquivalenceOfIso
    (pinchedHomIsoOfIso i (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)))
  simpa only [i, x, y, oppositeInternalHomIso_vertex] using h

/-- 概要：元の Fun の Hom の宇宙変更と、元の Hom 係数図式間の空間は同値。
方針：反対図式の Hom 同値を持ち上げ、内部 Hom の宇宙比較と co-Yoneda を合成する。
規約：F・G を選び直さない。両変数での全自然性はまだ主張しない。
使われ方：P-12 の end 比較の元の Hom 側の模型。 -/
def functorHomToHomWeightDiagramEquivalence
    {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (pinchedHom (functorVertex F) (functorVertex G)))
      (pinchedHom (functorVertex (presheafHomWeightDiagram G))
        (functorVertex (presheafHomWeightDiagram F))) := by
  let e := functorHomOppositeEquivalence F G
  let q := (IsQCatEquivalence.ulift.{u, u + 1} e.isQCatEquivalence).choose
  let i := uliftFunctorSpaceIso.{u, u + 1} A.op C.op
  let j := (uliftPinchedHomIso.{u, u + 1}
    (functorVertex (SSet.opFunctor.map G)) (functorVertex (SSet.opFunctor.map F))) ≪≫
    pinchedHomIsoOfIso i (ULift.up (functorVertex (SSet.opFunctor.map G)))
      (ULift.up (functorVertex (SSet.opFunctor.map F)))
  let h := q.trans (qCatEquivalenceOfIso j)
  have h' : QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (pinchedHom (functorVertex F) (functorVertex G)))
      (pinchedHom
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map G)))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F)))) := by
    simpa only [j, i, Iso.trans_hom, uliftFunctorSpaceIso_hom_vertex] using h
  exact h'.trans (homWeightDiagramHomEquivalence F G)

end SerrePositivity.InfinityCategories.F2.Presentable
