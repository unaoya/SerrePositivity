module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterDiagram

/-!
概要：実パラメータ図式の比較を、順序方向と入力 Hom の両方に自然な変換へ送る。
方針：元のパラメータ制限の混合 Hom を使い、自然性の可換式を全単体で保持する。
規約：パラメータ対象ごとの同型から全図式自然性を推論しない。
使われ方：共同 loop 図式の実終点と元のパラメータ単位を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 混合 Hom は、同じ元の源制限と同じ入力 Hom 作用の合成そのもの。 -/
lemma d3PointedKanMixed_eq_whiskerRight {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X Y : PointedKanObject.{u}) :
    d3PointedKanMixed i X Y = (d3PointedKanIhom A).map X Y ≫
      eHomWhiskerRight SSet
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) :
          (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom A).obj X)
        ((d3PointedKanIhom A).obj Y) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  rfl

/-- 混合 Hom は、同じ入力 Hom と終点での元の制限射の合成にも一致する。 -/
lemma d3PointedKanMixed_eq_whiskerLeft {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X Y : PointedKanObject.{u}) :
    d3PointedKanMixed i X Y = (d3PointedKanIhom B).map X Y ≫
      eHomWhiskerLeft SSet ((d3PointedKanIhom B).obj X)
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj) :
          (d3PointedKanIhom B).obj Y ⟶ (d3PointedKanIhom A).obj Y) :=
  (d3PointedKanMixed_eq_whiskerRight i X Y).trans
    (d3PointedKanPre_whiskered i X Y).symm

/-- 元の二つのパラメータ制限の合成は、同じ Kan 対象上でも厳密に合成する。 -/
lemma d3PointedKanRestriction_comp {A B C : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : C ⟶ A) (X : PointedKanObject.{u}) :
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i X.obj) :
      (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom A).obj X) ≫
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j X.obj) :
      (d3PointedKanIhom A).obj X ⟶ (d3PointedKanIhom C).obj X) =
    ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (j ≫ i) X.obj) := by
  apply ObjectProperty.hom_ext
  exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp j i X.obj

/-- 元の可換なパラメータ正方形は、混合 Hom の全単体の可換正方形を与える。 -/
lemma d3PointedKanMixed_square {A B C D : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (j : C ⟶ D) (p : C ⟶ A) (q : D ⟶ B)
    (h : p ≫ i = j ≫ q) (X Y : PointedKanObject.{u}) :
    d3PointedKanMixed i X Y ≫
      eHomWhiskerLeft SSet ((d3PointedKanIhom B).obj X)
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p Y.obj) :
          (d3PointedKanIhom A).obj Y ⟶ (d3PointedKanIhom C).obj Y) =
    d3PointedKanMixed j X Y ≫
      eHomWhiskerRight SSet
        (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed q X.obj) :
          (d3PointedKanIhom B).obj X ⟶ (d3PointedKanIhom D).obj X)
        ((d3PointedKanIhom C).obj Y) := by
  rw [d3PointedKanMixed_eq_whiskerLeft i, d3PointedKanMixed_eq_whiskerLeft j]
  simp only [Category.assoc]
  rw [eHom_whisker_exchange]
  rw [← Category.assoc ((d3PointedKanIhom D).map X Y),
    ← d3PointedKanPre_whiskered q X Y]
  simp only [Category.assoc]
  rw [← eHomWhiskerLeft_comp, ← eHomWhiskerLeft_comp,
    d3PointedKanRestriction_comp, d3PointedKanRestriction_comp, h]

section
open EnrichedOrderedCylinder
variable {J : Type} [Preorder J]
  {D E : Jᵒᵖ ⥤ PointedSimplicialSet.{u}} (η : D ⟶ E)

/-- 元のパラメータ比較は、順序方向と入力の全 Hom に同時に自然。 -/
lemma d3ParameterPre_whiskered (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J PointedKanObject.{u}) :
    (d3PointedKanParameterDiagram E).map X Y ≫ eHomWhiskerLeft SSet
      ((d3PointedKanParameterDiagram E).obj X)
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op Y.position)) Y.val.obj) :
        (d3PointedKanParameterDiagram E).obj Y ⟶ (d3PointedKanParameterDiagram D).obj Y) =
    (d3PointedKanParameterDiagram D).map X Y ≫ eHomWhiskerRight SSet
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj) :
        (d3PointedKanParameterDiagram E).obj X ⟶ (d3PointedKanParameterDiagram D).obj X)
      ((d3PointedKanParameterDiagram D).obj Y) := by
  dsimp only [d3PointedKanParameterDiagram, D3EnrichedOrderedDiagram.functor]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨p, f⟩
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  have hE := D3EnrichedOrderedDiagram.map_app
    (d3ParameterStage E) (d3ParameterMixed E) X Y d p f
  have hD := D3EnrichedOrderedDiagram.map_app
    (d3ParameterStage D) (d3ParameterMixed D) X Y d p f
  have hS := ConcreteCategory.congr_hom (NatTrans.congr_app
    (d3PointedKanMixed_square (d3ParameterArrow E p.down.down)
      (d3ParameterArrow D p.down.down) (η.app (Opposite.op Y.position))
      (η.app (Opposite.op X.position))
      (η.naturality (homOfLE p.down.down).op).symm X.val Y.val) d) f
  exact (congrArg (fun t ↦ (eHomWhiskerLeft SSet
    ((d3PointedKanIhom (E.obj (Opposite.op X.position))).obj X.val)
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op Y.position)) Y.val.obj) :
      (d3PointedKanIhom (E.obj (Opposite.op Y.position))).obj Y.val ⟶
        (d3PointedKanIhom (D.obj (Opposite.op Y.position))).obj Y.val)).app d t) hE).trans
    (hS.trans (congrArg (fun t ↦ (eHomWhiskerRight SSet
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj) :
        (d3PointedKanIhom (E.obj (Opposite.op X.position))).obj X.val ⟶
          (d3PointedKanIhom (D.obj (Opposite.op X.position))).obj X.val)
      ((d3PointedKanIhom (D.obj (Opposite.op Y.position))).obj Y.val)).app d t) hD).symm)

/-- パラメータ自然変換を、全順序円柱上の元の制限を成分とする豊穣変換へ送る。 -/
def d3ParameterPre : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
    (d3PointedKanParameterDiagram E) (d3PointedKanParameterDiagram D) where
  app X := eHomEquiv SSet (ObjectProperty.homMk
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj))
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj) :
      (d3PointedKanParameterDiagram E).obj X ⟶ (d3PointedKanParameterDiagram D).obj X)
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op Y.position)) Y.val.obj) :
      (d3PointedKanParameterDiagram E).obj Y ⟶ (d3PointedKanParameterDiagram D).obj Y)
    ((d3PointedKanParameterDiagram D).map X Y)
    ((d3PointedKanParameterDiagram E).map X Y)).mp
      (d3ParameterPre_whiskered η X Y).symm).symm

/-- 同じ coherent 変換も、元の同じパラメータ制限そのものを成分に持つ。 -/
lemma d3ParameterPre_component (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J PointedKanObject.{u}) :
    StrictEnrichedTransformation.componentHom _ _ (d3ParameterPre η) X =
    ObjectProperty.homMk
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj) := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet (ObjectProperty.homMk
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app (Opposite.op X.position)) X.val.obj) :
        (d3PointedKanParameterDiagram E).obj X ⟶
          (d3PointedKanParameterDiagram D).obj X))) = _
  exact Equiv.symm_apply_apply _ _
end

/-- パラメータ自然同型を、全順序・全 Hom を保持する coherent 関手同型へ送る。 -/
def d3ParameterPreFunctorIso {J : Type} [Preorder J]
    {D E : Jᵒᵖ ⥤ PointedSimplicialSet.{u}} (η : D ≅ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D)) :=
  StrictEnrichedTransformation.functorIso _ _ (d3ParameterPre η.hom) (fun X ↦ by
    rw [d3ParameterPre_component]
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
      (d3PointedKanPre_piIsomorphism (η.hom.app (Opposite.op X.position)) X.val))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
