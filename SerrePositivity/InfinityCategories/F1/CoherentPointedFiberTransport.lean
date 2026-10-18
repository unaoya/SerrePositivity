module

public import SerrePositivity.InfinityCategories.F1.WeightedCosliceTransport
public import SerrePositivity.InfinityCategories.F1.LeftPointHomEnriched
public import SerrePositivity.InfinityCategories.F1.UniverseReflection

/-!
概要：元の Kan 値の射と一点空間からの左 coslice の実際の fiber transport の比較。
方針：反転した一点 Hom の係数の標準同型を weighted coslice の transport 比較へ合成する。
規約：一点空間と終点の空間は標準の coherent 頂点で指定する。
使われ方：Kerodon Corollary 5.6.0.6、復元した left fibration の作用を元の空間値の射で回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：左 fiber の係数への標準同型は Kan 値通常図式の射と可換。
方針：反転した一点 Hom の自然同型の逆方向の自然性を使う。
規約：各成分は既存の pointedSpaceLeftCoefficientIso。
使われ方：Kerodon Corollary 5.6.0.6、実際の transport 比較の係数を元の射へ戻す。 -/
lemma pointedSpaceLeftCoefficientIso_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) {i j : I} (f : i ⟶ j) :
    (show (F.obj i).obj ⟶ (F.obj j).obj from F.map f) ≫
        (pointedSpaceLeftCoefficientIso (F.obj j)).hom =
      (pointedSpaceLeftCoefficientIso (F.obj i)).hom ≫
        ((HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
          SSet.opFunctor).map f) := by
  have h := (oppositePointHomDiagramIso F).inv.naturality f
  exact h

/-- 概要：元の Kan 複体を、その反転した値上の一点空間の左 coslice fiber へ写す。
方針：標準の係数の同型の後に既存の coherent な左 coslice 比較を合成する。
規約：始点も終点も coherentNerveVertex で指定する。
使われ方：Kerodon Corollary 5.6.0.6、Kan 値の射と実際の fiber transport の比較の成分。 -/
noncomputable def coherentPointedFiberComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveVertex (kanObjectOpFunctor.obj K)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso K).hom ≫
    HomotopyLimits.coherentCosliceFiberComparison pointKanObject (kanObjectOpFunctor.obj K)

/-- 概要：元の空間から左 coslice fiber への標準比較は同値。
方針：係数の厳密な同型と coherent な左 coslice 比較の同値を合成する。
規約：同値性は構成した実際の射そのものについて述べる。
使われ方：Kerodon Corollary 5.6.0.6、比較成分を使った fiber の作用の回収。 -/
lemma coherentPointedFiberComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (coherentPointedFiberComparison K) :=
  (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (pointedSpaceLeftCoefficientIso K))).isQCatEquivalence.comp
      (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence
        pointKanObject (kanObjectOpFunctor.obj K)).isQCatEquivalence

/-- 概要：Kan 値図式の元の射と反転した値上の左 coslice の標準 transport は比較を介して関手同型。
方針：反転した一点 Hom の transport 比較に係数の標準同型を前合成し、自然性で整理する。
規約：底の辺は反転した Kan 値の射の coherent な辺。
使われ方：Kerodon Corollary 5.6.0.6、left unstraightening の fiber 間の作用を元の図式で回収する。 -/
noncomputable def coherentPointedFiberComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫ coherentPointedFiberComparison (F.obj j))
      (coherentPointedFiberComparison (F.obj i) ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
          (coherentNerveVertex pointKanObject)))
            (coherentNerveEdge (kanObjectOpFunctor.map (F.map f)))) := by
  have e := FunctorIso.precomp
    (coherentCosliceFiberComparison_transportIso (F ⋙ kanObjectOpFunctor) pointKanObject f)
    ((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso (F.obj i)).hom)
  have h := congrArg (SSet.uliftFunctor.{u + 1, u}).map
    (pointedSpaceLeftCoefficientIso_naturality F f)
  rw [Functor.map_comp, Functor.map_comp] at h
  change FunctorIso
    (((SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso (F.obj i)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
          SSet.opFunctor).map f)) ≫
      HomotopyLimits.coherentCosliceFiberComparison pointKanObject
        (kanObjectOpFunctor.obj (F.obj j)))
    ((coherentPointedFiberComparison (F.obj i)) ≫
      edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject)))
          (coherentNerveEdge (kanObjectOpFunctor.map (F.map f)))) at e
  rw [← h] at e
  exact e

/-- 概要：任意の Kan 複体の射は反転した値上の一点 coslice の transport と比較を介して関手同型。
方針：射を二点の通常図式にまとめ、図式の transport 比較を適用する。
規約：元の射 f に対して底の辺は f の反転の coherent な辺。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の射への作用の具体的な回収。 -/
noncomputable def coherentPointedFiberComparison_morphismIso
    {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ coherentPointedFiberComparison L)
      (coherentPointedFiberComparison K ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
          (coherentNerveVertex pointKanObject)))
            (coherentNerveEdge (kanObjectOpFunctor.map f))) := by
  let F : ULift.{u} (Fin 2) ⥤ KanObject.{u} :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      ComposableArrows.mk₁ f
  exact coherentPointedFiberComparison_transportIso F
    (homOfLE (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 from by decide))

/-- 概要：一点 coslice の普遍 fiber の transport が同値かどうかは元の Kan 複体の射で判定できる。
方針：実際の transport との比較の関手同型と両端の比較の同値に二対三則を使う。
規約：反転した射を底の辺に使う左右の係数の規約を保持する。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の作用の同値性の検出。 -/
lemma coherentPointedFiberTransport_isQCatEquivalence_iff
    {K L : KanObject.{u}} (f : K ⟶ L) :
    IsQCatEquivalence
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveEdge (kanObjectOpFunctor.map f))) ↔
      IsQCatEquivalence (X := K.obj) (Y := L.obj) f := by
  have e := coherentPointedFiberComparison_morphismIso f
  have hK := coherentPointedFiberComparison_isQCatEquivalence K
  have hL := coherentPointedFiberComparison_isQCatEquivalence L
  rw [← isQCatEquivalence_ulift_iff_of_kan.{u, u + 1} f]
  constructor
  · intro h
    exact hL.cancel_right ((hK.comp h).ofFunctorIso e.symm)
  · intro h
    exact hK.cancel_left ((h.comp hL).ofFunctorIso e)

end SerrePositivity.InfinityCategories
