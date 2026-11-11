module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPostUncurry

/-!
概要：固定底上の全単体集合を相対関手空間で豊穣化する。
方針：底上の射の単位と相対合成の既存の法則を使う。
規約：全ての対象の射影に充填性を仮定せず、coherent nerve の quasicategory 性も主張しない。
使われ方：scaffold の共通始域を含む自然な復元 span の値域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 相対関手空間を豊穣 Hom として使うための、底上の対象の包み。 -/
def SimplicialOverObject (B : SSet.{u}) := {_p : Over B // True}

/-- 通常の射は元の底上の射。 -/
instance simplicialOverObject_category (B : SSet.{u}) : Category.{u} (SimplicialOverObject B) where
  Hom p q := p.val ⟶ q.val
  id p := 𝟙 p.val
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 全ての底上の対象の相対 Hom による豊穣構造。 -/
instance simplicialOverObject_enrichedCategory (B : SSet.{u}) :
    EnrichedCategory SSet.{u} (SimplicialOverObject B) where
  Hom p q := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom p.val.hom
  id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p.val
  comp p q r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p.val q.val r.val
  id_comp p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity_comp p.val q.val
  comp_id p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id p.val q.val
  assoc p q r s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_assoc p.val q.val r.val s.val

/-- 通常の底上の射と豊穣 Hom の零単体の整合性。 -/
instance simplicialOverObject_simplicialCategory (B : SSet.{u}) :
    SimplicialCategory (SimplicialOverObject B) where
  homEquiv {p q} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv p.val q.val
  homEquiv_id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_id p.val
  homEquiv_comp {p q r} f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_comp (a := p.val) (b := q.val) (c := r.val) f g

/-- left fibrations の対象を全ての底上の対象へ含める豊穣関手。 -/
def leftFibrationOverEnriched (B : SSet.{u}) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (SimplicialOverObject B) where
  obj p := ⟨p.val, trivial⟩
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp
    rfl

/-- 対象の射と豊穣 Hom 全体の可換性を持つ、底上の豊穣関手の比較。 -/
def SimplicialOverComparison {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {B : SSet.{u}} (F G : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :=
  {η : ∀ X, (F.obj X).val ⟶ (G.obj X).val // ∀ X Y,
    F.map X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (F.obj Y).val.hom (G.obj Y).val.hom
      (η Y).left (η Y).w (F.obj X).val.hom =
    G.map X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre (G.obj Y).val.hom (η X)}

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
