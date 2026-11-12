module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSpecifiedFrameComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeOrdinaryHomKan

/-!
概要：元の AW 単位を、実 pinched 比較の同じ選択した逆を通して照合する。
方針：二つの混合単位三角形と E2 の実逆の anodyne 像の逆則を使う。
規約：生の辺の等式ではなく、同じ指定比較の反転後の等式を保持する。
使われ方：β6 f4c の元の射・指定底の零単体正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R))
attribute [local instance] EInfinity.DGAlgebra.modelCategory

/-- 同じ元の全 ordinary Hom 単位は、AW と選択 right frame の実比較後に一致する。 -/
lemma multiplicativeCellMappingPinchedEquivalence_unit_Q :
    SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((nativeCellMappingUnitLarge R A).app B ≫
        (multiplicativeCellMappingPinchedEquivalence R A B).hom) =
    SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((nativeCellChosenRightMappingUnitLarge R A).app B ≫
        (nativeCellSpecifiedFramePinchedEquivalence R A B).hom) := by
  let Q := SimplicialModel.AnodyneHomotopy.anodyneQ
  let L := (nativeCellMixedLeftLarge_isQCatEquivalence R A B).choose
  let C := (nativeCellChosenMixedRightLarge_isQCatEquivalence R A B).choose
  have h₁ := congrArg (fun t => Q.map (t.app B))
    (nativeCellMappingUnitLarge_mixed_triangle R A)
  have h₂ := congrArg (fun t => Q.map (t.app B))
    (nativeCellChosenRightMappingUnitLarge_mixed_triangle R A)
  simp only [NatTrans.comp_app, Functor.map_comp] at h₁ h₂
  have hL := EInfinity.FrameHom.qCatEquivalence_hom_inv_Q L
  have hC := EInfinity.FrameHom.qCatEquivalence_hom_inv_Q C
  change Q.map ((nativeCellMixedLeftLarge R A).app B) ≫ Q.map L.inv = 𝟙 _ at hL
  change Q.map ((nativeCellChosenMixedRightLarge R A).app B) ≫ Q.map C.inv = 𝟙 _ at hC
  have h₁' : (Q.map ((nativeCellMappingUnitLarge R A).app B) ≫
      Q.map ((nativeCellMixedRightLarge R A).app B)) ≫ Q.map L.inv =
        Q.map ((nativeCellSourceFrameMappingUnitLarge R A).app B) := by
    rw [← h₁, Category.assoc, hL, Category.comp_id]
  have h₂' : (Q.map ((nativeCellSourceFrameMappingUnitLarge R A).app B) ≫
      Q.map ((nativeCellChosenMixedLeftLarge R A).app B)) ≫ Q.map C.inv =
        Q.map ((nativeCellChosenRightMappingUnitLarge R A).app B) := by
    rw [h₂, Category.assoc, hC, Category.comp_id]
  change Q.map ((nativeCellMappingUnitLarge R A).app B ≫
    ((nativeCellMixedRightLarge R A).app B ≫ L.inv ≫
      (nativeCellChosenMixedLeftLarge R A).app B ≫ C.inv ≫
        (nativeCellSpecifiedFramePinchedEquivalence R A B).hom)) = _
  simp only [Functor.map_comp]
  calc
    _ = ((Q.map ((nativeCellMappingUnitLarge R A).app B) ≫
          Q.map ((nativeCellMixedRightLarge R A).app B)) ≫ Q.map L.inv) ≫
        (Q.map ((nativeCellChosenMixedLeftLarge R A).app B) ≫ Q.map C.inv ≫
          Q.map (nativeCellSpecifiedFramePinchedEquivalence R A B).hom) := by
      simp only [Category.assoc]
    _ = Q.map ((nativeCellSourceFrameMappingUnitLarge R A).app B) ≫
        (Q.map ((nativeCellChosenMixedLeftLarge R A).app B) ≫ Q.map C.inv ≫
          Q.map (nativeCellSpecifiedFramePinchedEquivalence R A B).hom) := by rw [h₁']
    _ = ((Q.map ((nativeCellSourceFrameMappingUnitLarge R A).app B) ≫
        Q.map ((nativeCellChosenMixedLeftLarge R A).app B)) ≫ Q.map C.inv) ≫
          Q.map (nativeCellSpecifiedFramePinchedEquivalence R A B).hom := by
      simp only [Category.assoc]
    _ = _ := by rw [h₂']

/-- 同じ元の dg 射を ordinary Hom の一定零単体として保持する。 -/
def nativeCellOrdinaryPoint (f : cellResolution R A ⟶ B) :
    (𝟙_ SSet.{u + 1}) ⟶ (nativeCellOrdinaryLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj B :=
  SSet.const (ULift.up f)

/-- 選択 right frame の零単体は E2 の同じ元の射の単位点。 -/
lemma nativeCellOrdinaryPoint_chosenRight (f : cellResolution R A ⟶ B) :
    nativeCellOrdinaryPoint R A B f ≫ (nativeCellChosenRightMappingUnitLarge R A).app B =
      EInfinity.FrameHom.rightFrameHammockUnitPoint
        ((EInfinity.DGAlgebra.sourceFrameFamily R).atObject (cellResolution R A))
        (EInfinity.DGAlgebra.rightFrameFamily R) f 0 := by
  rw [nativeCellOrdinaryPoint, SSet.const_comp]
  rfl

/-- AW の元の射の単位点も、同じ hammock 射と指定局所化三角形へ戻る。 -/
lemma multiplicativeCellMappingPinchedEquivalence_point_Q (f : cellResolution R A ⟶ B) :
    SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((nativeCellOrdinaryPoint R A B f ≫ (nativeCellMappingUnitLarge R A).app B) ≫
        (multiplicativeCellMappingPinchedEquivalence R A B).hom) =
    SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).weakEquivalences
        (AsSmall.up.map f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
        EInfinity.SimplicialLocalization.kanHammockHomPinchedMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) (cellResolution R A))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) B) ≫
        ((nativeFrameLocalizationComparison R).pinchedEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
            (Mon (Complex R)) (cellResolution R A)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
            (Mon (Complex R)) B))).hom) := by
  let Q := SimplicialModel.AnodyneHomotopy.anodyneQ
  have h := congrArg (fun t => Q.map (nativeCellOrdinaryPoint R A B f) ≫ t)
    (multiplicativeCellMappingPinchedEquivalence_unit_Q R A B)
  have h' : Q.map ((nativeCellOrdinaryPoint R A B f ≫
      (nativeCellMappingUnitLarge R A).app B) ≫
        (multiplicativeCellMappingPinchedEquivalence R A B).hom) =
      Q.map ((nativeCellOrdinaryPoint R A B f ≫
        (nativeCellChosenRightMappingUnitLarge R A).app B) ≫
          (nativeCellSpecifiedFramePinchedEquivalence R A B).hom) := by
    simpa only [Functor.map_comp, Category.assoc] using! h
  exact h'.trans (by
    rw [nativeCellOrdinaryPoint_chosenRight]
    exact nativeCellSpecifiedFramePinchedEquivalence_unit_Q R A B f)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
