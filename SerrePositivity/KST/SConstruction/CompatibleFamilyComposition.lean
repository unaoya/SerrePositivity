module
public import SerrePositivity.KST.Spectra.SpectrumMappingComposition
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition

/-! # 一方の構造適合で他方の実円柱を射影する合成則
概要：前の族の厳密な構造適合を使い、合成族の射影を後ろの円柱の射影へ移す。
方針：豊穣合成の前合成自然性と中間射の交換、suspension の合成保存を使う。
規約：円柱の全時刻と元の写像空間を保つ。
使われ方：K 合成補正の後半の全射影 trace の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v w u z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Spectra

/-- 前の族だけが構造射と整合するとき、合成の射影を後ろの族の射影へ移せる。 -/
lemma enriched_left_compatible_comp (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type z} [Category.{w} C] [EnrichedOrdinaryCategory V C] (F : EnrichedFunctor V C C)
    {X Y X' Y' Z' : C} (sx : F.obj X ⟶ X') (sy : F.obj Y ⟶ Y')
    {P Q : V} (a : P ⟶ (X ⟶[V] Y)) (a' : P ⟶ (X' ⟶[V] Y'))
    (b' : Q ⟶ (Y' ⟶[V] Z'))
    (ha : a' ≫ eHomWhiskerRight V sx Y' = a ≫ F.map X Y ≫ eHomWhiskerLeft V (F.obj X) sy) :
    (a' ⊗ₘ b') ≫ eComp V X' Y' Z' ≫ eHomWhiskerRight V sx Z' =
      ((a ≫ F.map X Y) ⊗ₘ (b' ≫ eHomWhiskerRight V sy Z')) ≫ eComp V (F.obj X) (F.obj Y) Z' := by
  rw [eComp_eHomWhiskerRight, ← Category.assoc, tensorHom_comp_whiskerRight, ha]
  rw [← Category.assoc a (F.map X Y)]
  rw [← tensorHom_comp_whiskerRight (a ≫ F.map X Y)
    (eHomWhiskerLeft V (F.obj X) sy) b', Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_comp_middle]
  rw [← Category.assoc, tensorHom_comp_whiskerLeft]

/-- 豊穣関手で写した二族の合成と、後続構造射との後合成を交換する。 -/
lemma enriched_functor_comp_post (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type z} [Category.{w} C] [EnrichedOrdinaryCategory V C] (F : EnrichedFunctor V C C)
    {X Y Z Z' : C} (sz : F.obj Z ⟶ Z') {P Q : V}
    (a : P ⟶ (X ⟶[V] Y)) (b : Q ⟶ (Y ⟶[V] Z)) :
    ((a ≫ F.map X Y) ⊗ₘ (b ≫ F.map Y Z ≫ eHomWhiskerLeft V (F.obj Y) sz)) ≫
        eComp V (F.obj X) (F.obj Y) Z' =
      (a ⊗ₘ b) ≫ eComp V X Y Z ≫ F.map X Z ≫ eHomWhiskerLeft V (F.obj X) sz := by
  rw [← Category.assoc b (F.map Y Z)]
  rw [← tensorHom_comp_whiskerLeft (a ≫ F.map X Y) (b ≫ F.map Y Z)
    (eHomWhiskerLeft V (F.obj Y) sz), Category.assoc, ← eComp_eHomWhiskerLeft,
    ← tensorHom_comp_tensorHom, Category.assoc, ← EnrichedFunctor.map_comp_assoc]

universe t
local instance compatibleFamilyCompositionPointedCategory :
    SimplicialCategory PointedSimplicialSet.{t} := PointedEnrichment.simplicialCategory

/-- 共通パラメータの対角からテンソルした二族への合成は同じ二族の積である。 -/
lemma familyDiagonal_tensorHom {D E F : SSet.{t}} (a : D ⟶ E) (b : D ⟶ F) :
    lift (𝟙 D) (𝟙 D) ≫ (a ⊗ₘ b) = lift a b := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

/-- 共通パラメータ上でも、前の族の厳密適合によって後ろの実円柱を射影する。 -/
lemma pointed_left_compatible_lift {D : SSet.{t}} {X Y X' Y' Z' : PointedSimplicialSet.{t}}
    (sx : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ⟶ X') (sy : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y ⟶ Y')
    (a : D ⟶ (PointedObject.basedHom X Y).right)
    (a' : D ⟶ (PointedObject.basedHom X' Y').right)
    (b' : D ⟶ (PointedObject.basedHom Y' Z').right)
    (ha : a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre sx Y' = a ≫ (suspensionHom X Y).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) sy).right) :
    lift a' b' ≫ eComp SSet X' Y' Z' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre sx Z' =
      lift (a ≫ (suspensionHom X Y).right) (b' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre sy Z') ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z' := by
  have h := enriched_left_compatible_comp SSet suspensionEnrichedFunctor sx sy a a' b'
    (by simpa only [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
      suspensionEnrichedFunctor] using ha)
  have hd := congrArg (fun q => lift (𝟙 D) (𝟙 D) ≫ q) h
  simpa only [PointedEnrichment.whiskerRight_eq, suspensionEnrichedFunctor,
    ← Category.assoc, familyDiagonal_tensorHom] using hd

/-- suspension した二族を合成して構造射で写すことは、元の合成の段の境界比較に一致する。 -/
lemma pointed_suspension_comp_lift {D : SSet.{t}} {X Y Z Z' : PointedSimplicialSet.{t}}
    (sz : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Z ⟶ Z')
    (a : D ⟶ (PointedObject.basedHom X Y).right)
    (b : D ⟶ (PointedObject.basedHom Y Z).right) :
    lift (a ≫ (suspensionHom X Y).right)
      (b ≫ (suspensionHom Y Z).right ≫ (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) sz).right) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z' =
      lift a b ≫ eComp SSet X Y Z ≫ (suspensionHom X Z).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) sz).right := by
  have h := enriched_functor_comp_post SSet suspensionEnrichedFunctor sz a b
  have hd := congrArg (fun q => lift (𝟙 D) (𝟙 D) ≫ q) h
  simpa only [PointedEnrichment.whiskerLeft_eq, suspensionEnrichedFunctor,
    ← Category.assoc, familyDiagonal_tensorHom] using hd

end SerrePositivity.KST.SConstruction
