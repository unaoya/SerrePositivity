module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeChosenFrameCoherent
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinityVertices
public import SerrePositivity.DifferentialGraded.Algebras.FrameComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveULiftHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakDeformationSource

/-!
概要：E2 の実 right frame 比較を、Sp の元の全擬同型局所化へ適用する。
方針：AsSmall と ULiftHom の全 nerve の実同型で源を合わせ、同じ cell 源を使う。
規約：モデル構造・関手的分解を入力せず、指定局所化と元の全擬同型を保持する。
使われ方：β6 f4c の実 pinched 比較と、その全標的接続の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory _root_.HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]
attribute [local instance] _root_.SerrePositivity.DGAlgebra.modelCategory

/-- 同じ全対象・全射の二つの宇宙表示の実 nerve 同型。 -/
def nativeModelInfinityPresentationIso :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ≅
      nerve (InfinityPresentation R) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso _ ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.iso _).symm

/-- E2 の全対象表示上の指定射。標的は元の edgeLocalization のまま。 -/
def nativeModelQuasiIsoInfinityMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ quasiIsoInfinity R :=
  (nativeModelInfinityPresentationIso R).hom ≫ quasiIsoInfinityMap R

/-- 源の宇宙表示を変えても元の局所化頂点を厳密に保持する。 -/
@[simp] lemma nativeModelQuasiIsoInfinityMap_vertex (A : Mon (Complex R)) :
    (nativeModelQuasiIsoInfinityMap R).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) A)) =
        quasiIsoInfinityVertex R A := rfl

/-- 元の dg 射の局所化辺も全く同じ一単体。 -/
lemma nativeModelQuasiIsoInfinityMap_edge {A B : Mon (Complex R)} (f : A ⟶ B) :
    ((nerve.edgeMk (AsSmall.up.map f)).map (nativeModelQuasiIsoInfinityMap R)).edge =
      ((nerve.edgeMk ((infinityPresentationFunctor R).map f)).map
        (quasiIsoInfinityMap R)).edge := by
  apply congrArg ((quasiIsoInfinityMap R).app (Opposite.op ⦋1⦌))
  exact ComposableArrows.ext₁ rfl rfl (by simp; rfl)


/-- 同じ実宇宙同型で全擬同型の局所化を輸送する。 -/
lemma nativeModelQuasiIsoInfinity_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (nativeModelQuasiIsoInfinityMap R)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))) := by
  let a := nativeModelInfinityPresentationIso R
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakDeformationSource.transfer a.inv a.hom (quasiIsoInfinityMap R)
    (quasiIsoInfinityEdges R)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))))
  · intro s hs
    obtain ⟨X, Y, f, rfl⟩ := ComposableArrows.mk₁_surjective s
    refine ⟨_, _, (a.inv.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)).hom, ?_,
      (ComposableArrows.mk₁_hom _).symm⟩
    exact hs
  · rintro s ⟨X, Y, f, hf, rfl⟩
    exact hf
  · exact quasiIsoInfinity_isLocalization R
  · intro E _
    rw [a.inv_hom_id]
    simp only [MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id]
    exact ⟨Iso.refl _⟩
  · intro E _
    rw [a.hom_inv_id]
    simp only [MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id]
    exact ⟨Iso.refl _⟩

/-- 指定局所化への実比較関手と同じ三角形を保持する。 -/
def nativeFrameLocalizationComparison :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CoherentLocalizationComparison
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))))
      (nativeModelQuasiIsoInfinityMap R) :=
  _root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R (nativeModelQuasiIsoInfinityMap R)
    (nativeModelQuasiIsoInfinity_isLocalization R)

/-- 元の cell 源と任意標的の選択 right frame は、元の局所化の pinched Hom と同値。 -/
def nativeCellSpecifiedFramePinchedEquivalence (A B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((nativeCellChosenRightLargeKanFunctor R A).obj B).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (quasiIsoInfinityVertex R (cellResolution R A))
        (quasiIsoInfinityVertex R B)) := by
  exact _root_.SerrePositivity.DGAlgebra.framePinchedEquivalence R (nativeModelQuasiIsoInfinityMap R)
    (nativeModelQuasiIsoInfinity_isLocalization R) (cellResolution R A)
    (cellResolution_isCofibrant R A) B

/-- 実 E2 の六辺比較と指定局所化の三角形を、同じ cell 源に適用する。
終端の表現可能関手への全図式接続は別途保持する。 -/
def nativeCellFrameHammockCoherentComparison (A : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
        (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 0)
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
        (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 6) :=
  (_root_.SerrePositivity.DGAlgebra.frameCoherentComparison R (nativeModelQuasiIsoInfinityMap R)
    (nativeModelQuasiIsoInfinity_isLocalization R) (cellResolution R A)
    (cellResolution_isCofibrant R A)).1

/-- 同じ frame 比較の単位点は、同じ実 hammock 射と指定三角形の輸送を回収する。 -/
lemma nativeCellSpecifiedFramePinchedEquivalence_unit_Q (A B : Mon (Complex R))
    (f : cellResolution R A ⟶ B) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint
        ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
        (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) f 0 ≫
          (nativeCellSpecifiedFramePinchedEquivalence R A B).hom) =
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) (cellResolution R A))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) B) ≫
        ((nativeFrameLocalizationComparison R).pinchedEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) (cellResolution R A)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) B))).hom) :=
  _root_.SerrePositivity.DGAlgebra.framePinchedEquivalence_unit_Q R (nativeModelQuasiIsoInfinityMap R)
    (nativeModelQuasiIsoInfinity_isLocalization R) (cellResolution R A)
    (cellResolution_isCofibrant R A) B f

/-- 指定三角形の両端成分で共役すると、元の dg 射の局所化を回収する。 -/
lemma nativeFrameOriginalArrow_conjugation {A B : Mon (Complex R)} (f : A ⟶ B) :
    let c := nativeFrameLocalizationComparison R
    let x := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) A)
    let y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) B)
    (c.triangle.toNatIso.app (HomotopyCategory.mk x)).inv ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))) ≫
        c.equivalence.hom)).toFunctor.map
          (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) ≫
      (c.triangle.toNatIso.app (HomotopyCategory.mk y)).hom =
        (hoFunctor.map (nativeModelQuasiIsoInfinityMap R)).toFunctor.map
          (HomotopyCategory.homMk (nerve.edgeMk (AsSmall.up.map f)).toTruncated) := by
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFrameOriginalArrow_conjugation
    (G := nativeModelQuasiIsoInfinityMap R) (X := A)
    (K := (nativeFrameLocalizationComparison R).equivalence.hom)
    (e := (nativeFrameLocalizationComparison R).triangle) f

/-- 元の AW 写像模型も、同じ実混合比較を通じて指定局所化の Hom と同値。
これは各標的の実同値であり、全表現可能関手との同型の代用にはしない。 -/
def multiplicativeCellMappingPinchedEquivalence (A B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((multiplicativeCellMappingLargeKanFunctor R A).obj B).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (quasiIsoInfinityVertex R (cellResolution R A))
        (quasiIsoInfinityVertex R B)) :=
  (nativeCellMixedRightLarge_isQCatEquivalence R A B).choose |>.trans
    ((nativeCellMixedLeftLarge_isQCatEquivalence R A B).choose.symm.trans
      ((nativeCellChosenMixedLeftLarge_isQCatEquivalence R A B).choose.trans
        ((nativeCellChosenMixedRightLarge_isQCatEquivalence R A B).choose.symm.trans
          (nativeCellSpecifiedFramePinchedEquivalence R A B))))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
