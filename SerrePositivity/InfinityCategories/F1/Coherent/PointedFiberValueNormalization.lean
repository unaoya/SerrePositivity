module

public import SerrePositivity.InfinityCategories.F1.Coherent.CosliceFiberValueCommonRecovery
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue

/-!
概要：標準の pointed-space 値回収を、同じ coherent 頂点表示へ厳密に正規化する。
方針：頂点の等号による pinched Hom の移送を明示し、既存の値回収をそのまま使う。
規約：全 fiber で選ばれた比較射を保ち、別の値同値を選ばない。
使われ方：Ind-S (5) の全族単位の同じ fiber 内での回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 頂点表示の移送は、既存の左右 Hom 比較と厳密に可換。 -/
lemma pinchedHomLeftRightEquivalence_endpoint_naturality
    {X : SSet.{u}} [Quasicategory X] {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    (eqToIso (congrArg₂ (fun a b => pinchedHomLeft a b) hx hy)).hom ≫
      (pinchedHomLeftRightEquivalence x' y').hom =
    (pinchedHomLeftRightEquivalence x y).hom ≫
      (eqToIso (congrArg₂ (fun a b => pinchedHom a b) hx hy)).hom := by
  subst x'
  subst y'
  simp

/-- 左 fiber と pinched Hom の同型も、両端の頂点の表示移送と可換。 -/
lemma cosliceFiberPinchedLeftIso_endpoint_naturality
    {X : SSet.{u}} {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y') :
    eqToHom (congrArg₂ (fun a b =>
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm a)) b) hx hy) ≫
      (cosliceFiberPinchedLeftIso x' y').hom =
    (cosliceFiberPinchedLeftIso x y).hom ≫
      eqToHom (congrArg₂ (fun a b => pinchedHomLeft a b) hx hy) := by
  subst x'
  subst y'
  simp

/-- coherent な頂点表示の左 fiber から標準 pointed-space fiber への同じ表示移送。 -/
def coherentPointedFiberNormalization (K : KanObject.{u}) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
      (coherentNerveVertex K) ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K) :=
  (cosliceFiberPinchedLeftIso (coherentNerveVertex pointKanObject) (coherentNerveVertex K)).hom ≫
    (eqToIso (congrArg₂ (fun a b => pinchedHomLeft a b)
      (spaceInfinityVertex_eq_coherent pointKanObject)
      (spaceInfinityVertex_eq_coherent K))).inv ≫
    (pointedSpaceFiberPinchedLeftIso (spaceInfinityVertex K)).inv

/-- 正規化は両端の表示の等号が与える標準移送そのもの。 -/
lemma coherentPointedFiberNormalization_eq (K : KanObject.{u}) :
    coherentPointedFiberNormalization K = eqToHom (congrArg₂ (fun a b =>
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm a)) b)
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm) := by
  apply (cancel_mono (pointedSpaceFiberPinchedLeftIso (spaceInfinityVertex K)).hom).1
  simpa only [coherentPointedFiberNormalization, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, eqToIso.inv, pointedSpaceFiberPinchedLeftIso, pointSpaceVertex] using
    (cosliceFiberPinchedLeftIso_endpoint_naturality
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm).symm

/-- 標準の pointed-space 値回収は、同じ coherent 頂点での右 Hom 回収そのもの。 -/
lemma coherentPointedFiberNormalization_value (K : KanObject.{u}) :
    coherentPointedFiberNormalization K ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom =
    (cosliceFiberPinchedLeftIso (coherentNerveVertex pointKanObject) (coherentNerveVertex K)).hom ≫
      (pinchedHomLeftRightEquivalence (coherentNerveVertex pointKanObject) (coherentNerveVertex K)).hom ≫
      (coherentHomEquivalence pointKanObject K).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (pointKanObjectHomIso K).hom := by
  have hr : (pointSpaceRightMappingEquivalence K).hom =
      (eqToIso (congrArg₂ (fun a b => pinchedHom a b)
        (spaceInfinityVertex_eq_coherent pointKanObject)
        (spaceInfinityVertex_eq_coherent K))).hom ≫
      (coherentHomEquivalence pointKanObject K).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (pointKanObjectHomIso K).hom := by
    rfl
  simp only [coherentPointedFiberNormalization, pointedSpaceFiberValueEquivalence,
    QCatEquivalence.trans, qCatEquivalenceOfIso,
    Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ _ ≫ _ ≫ (pointSpaceRightMappingEquivalence K).hom = _
  rw [hr]
  have hn := pinchedHomLeftRightEquivalence_endpoint_naturality
    (spaceInfinityVertex_eq_coherent pointKanObject) (spaceInfinityVertex_eq_coherent K)
  erw [← reassoc_of% hn]

/-- 既存の指定値回収は、fiber と値の同時表示移送と厳密に可換。 -/
lemma pointedSpaceFiberValueEquivalence_endpoint_naturality
    {s t : SpaceInfinity.{u} _⦋0⦌} (h : s = t) :
    (pointedSpaceFiberValueEquivalence s).hom ≫
      eqToHom (congrArg (fun z => (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject z).obj) h) =
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) h) ≫
      (pointedSpaceFiberValueEquivalence t).hom := by
  subst t
  simp

/-- 共通解像上の左比較を、同じ標準 pointed-space 値回収へ送ると右射影になる。 -/
def coherentPointedFiberValueCommonIso (K : KanObject.{u}) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (edgewiseLeft K.obj ≫ SSet.opFunctor.map (pointKanObjectHomIso K).inv) ≫
        HomotopyLimits.coherentCosliceFiberComparison pointKanObject K ≫
        coherentPointedFiberNormalization K ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight K.obj)) := by
  have e := FunctorIso.postcomp (FunctorIso.precomp
    (coherentCosliceFiberValueCommonIso pointKanObject K)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseSubdivisionMap (pointKanObjectHomIso K).inv)))
    ((SSet.uliftFunctor.{u + 1, u}).map (pointKanObjectHomIso K).hom)
  rw [← Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseSubdivisionMap (pointKanObjectHomIso K).inv))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (edgewiseLeft (SimplicialCategory.sHom pointKanObject K))),
    ← Functor.map_comp, edgewiseLeft_naturality] at e
  erw [coherentPointedFiberNormalization_value K]
  simpa only [Category.assoc, ← Functor.map_comp, edgewiseLeft_naturality,
    edgewiseRight_naturality, Iso.inv_hom_id, Category.comp_id] using e

end SerrePositivity.InfinityCategories
