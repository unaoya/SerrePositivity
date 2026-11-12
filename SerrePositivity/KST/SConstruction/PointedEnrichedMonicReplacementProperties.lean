module
public import SerrePositivity.KST.Spectra.FreeInterval
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacement
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderMono
public import SerrePositivity.KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence

/-! # 同じ関手的 Kan 単射置換の無条件の性質
概要：同じ置換の源比較は単射、標的比較は anodyne で、元の射を局所化で回収する。
方針：元の円柱の性質に同じ Ex∞ 単位を合成する。
規約：入力射に単射性や弱同値性を仮定しない。使われ方：BF の最初の帰納段。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 同じ元の置換の値は、実際の Ex∞ Kan 複体。 -/
lemma pointedEnrichedMonicReplacement_kanComplex (X : C) :
    KanComplex (((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 同じ実写像円柱から置換への元の単位は、基礎 anodyne 射。 -/
lemma pointedEnrichedMonicReplacementUnit_anodyne (X : C) :
    anodyneExtensions
      (show ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj ⟶
        ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj from
          pointedEnrichedMonicReplacementUnit F G t h X).right :=
  exInfinityPointedUnit_anodyne ((pointedEnrichedMappingCylinderFunctor F G t h).obj X)

/-- 元の標的から同じ Kan 置換への比較は、基礎 anodyne 射。 -/
lemma pointedEnrichedMonicReplacementTarget_anodyne (X : C) :
    anodyneExtensions
      (show (G.obj X).obj ⟶ ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj from
        pointedEnrichedMonicReplacementTarget F G t h X).right :=
  anodyneExtensions.comp_mem _ _
    (pointedTensorMappingCylinderTarget_anodyne (show (F.obj X).obj ⟶ (G.obj X).obj from t X))
    (pointedEnrichedMonicReplacementUnit_anodyne F G t h X)

/-- 元の源から同じ Kan 置換への比較は、基礎単体集合上で単射。 -/
lemma pointedEnrichedMonicReplacementSource_mono (X : C) :
    Mono (show (F.obj X).obj ⟶ ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj from
      pointedEnrichedMonicReplacementSource F G t h X).right := by
  let f : (F.obj X).obj ⟶ (G.obj X).obj := t X
  let η : pointedTensorMappingCylinder f ⟶
      ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj :=
    pointedEnrichedMonicReplacementUnit F G t h X
  let _ : Mono η.right := Spectra.anodyne_mono _
    (pointedEnrichedMonicReplacementUnit_anodyne F G t h X)
  change Mono ((pointedTensorMappingCylinderSource f).right ≫ η.right)
  infer_instance

/-- 同じ単射置換の源比較は、局所化で元の射と標的比較の合成を回収する。 -/
lemma pointedEnrichedMonicReplacementSource_localized_eq
    {D : Type w} [Category.{z} D] (L : SSet.{u} ⥤ D)
    (hL : anodyneExtensions.IsInvertedBy L) (X : C) :
    L.map
        (show (F.obj X).obj ⟶ ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj from
          pointedEnrichedMonicReplacementSource F G t h X).right =
      L.map (show (F.obj X).obj ⟶ (G.obj X).obj from t X).right ≫
        L.map (show (G.obj X).obj ⟶
          ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj from
            pointedEnrichedMonicReplacementTarget F G t h X).right := by
  let f : (F.obj X).obj ⟶ (G.obj X).obj := t X
  let η : pointedTensorMappingCylinder f ⟶
      ((pointedEnrichedMonicReplacementFunctor F G t h).obj X).obj :=
    pointedEnrichedMonicReplacementUnit F G t h X
  change L.map ((pointedTensorMappingCylinderSource f).right ≫ η.right) =
    L.map f.right ≫ L.map ((pointedTensorMappingCylinderTarget f).right ≫ η.right)
  simp only [L.map_comp, ← Category.assoc]
  rw [pointedTensorMappingCylinderSource_localized_eq L hL f]

end SerrePositivity.KST.SConstruction
