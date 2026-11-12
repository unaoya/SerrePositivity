module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison
public import Mathlib.CategoryTheory.Enriched.Opposite

/-!
概要：二つの単体的圏の Hom を同時に動かす積の豊穣圏。
方針：Hom の直積に成分ごとの単位と合成を入れ、underlying category を使う。
規約：対象の直積を包んで、元の通常の積圏とは独立に豊穣構造を指定する。
使われ方：復元 span の始域とテスト標的を全高次で同時に動かす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- Hom の直積で豊穣化するための対象の対。 -/
def SimplicialPairObject (C : Type v) (D : Type w) := C × D

/-- 豊穣 Hom の対を、それぞれの成分で同時に合成する。 -/
def simplicialPairComposition {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (X Y Z : SimplicialPairObject C D) :
    (SimplicialCategory.sHom X.1 Y.1 ⊗ SimplicialCategory.sHom X.2 Y.2) ⊗
      (SimplicialCategory.sHom Y.1 Z.1 ⊗ SimplicialCategory.sHom Y.2 Z.2) ⟶
        SimplicialCategory.sHom X.1 Z.1 ⊗ SimplicialCategory.sHom X.2 Z.2 :=
  let A := SimplicialCategory.sHom X.1 Y.1
  let B := SimplicialCategory.sHom X.2 Y.2
  let L := SimplicialCategory.sHom Y.1 Z.1
  let R := SimplicialCategory.sHom Y.2 Z.2
  lift
    (lift (fst (A ⊗ B) (L ⊗ R) ≫ fst A B)
      (snd (A ⊗ B) (L ⊗ R) ≫ fst L R) ≫ eComp SSet X.1 Y.1 Z.1)
    (lift (fst (A ⊗ B) (L ⊗ R) ≫ snd A B)
      (snd (A ⊗ B) (L ⊗ R) ≫ snd L R) ≫ eComp SSet X.2 Y.2 Z.2)

/-- Hom の直積と成分ごとの法則は豊穣圏をなす。 -/
instance simplicialPairObject_enrichedCategory {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    EnrichedCategory SSet.{u} (SimplicialPairObject C D) where
  Hom X Y := SimplicialCategory.sHom X.1 Y.1 ⊗ SimplicialCategory.sHom X.2 Y.2
  id X := lift (eId SSet X.1) (eId SSet X.2)
  comp X Y Z := simplicialPairComposition X Y Z
  id_comp X Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n f) (e_id_comp SSet X.1 Y.1)
    · exact congrArg (fun k ↦ k.app n g) (e_id_comp SSet X.2 Y.2)
  comp_id X Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n f) (e_comp_id SSet X.1 Y.1)
    · exact congrArg (fun k ↦ k.app n g) (e_comp_id SSet X.2 Y.2)
  assoc W X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨f, g⟩, ⟨⟨h, i⟩, ⟨j, k⟩⟩⟩
    apply Prod.ext
    · exact congrArg (fun a ↦ a.app n (f, h, j)) (e_assoc SSet W.1 X.1 Y.1 Z.1)
    · exact congrArg (fun a ↦ a.app n (g, i, k)) (e_assoc SSet W.2 X.2 Y.2 Z.2)

/-- 対の豊穣圏にはその underlying category を入れる。 -/
instance simplicialPairObject_category {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    Category.{u} (SimplicialPairObject C D) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (SimplicialPairObject C D)))

/-- underlying category と同じ豊穣 Hom は単体的圏をなす。 -/
instance simplicialPairObject_simplicialCategory {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    SimplicialCategory (SimplicialPairObject C D) where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := SimplicialPairObject C D) X
  homEquiv_comp f g :=
    ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := SimplicialPairObject C D) f g

/-- 元の二圏が局所 Kan なら対の圏も局所 Kan。 -/
instance simplicialPairObject_sHom_kanComplex {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)] (X Y : SimplicialPairObject C D) :
    KanComplex (SimplicialCategory.sHom X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨f, hf⟩ := KanComplex.hornFilling
    (σ ≫ fst (SimplicialCategory.sHom X.1 Y.1) (SimplicialCategory.sHom X.2 Y.2))
  obtain ⟨g, hg⟩ := KanComplex.hornFilling
    (σ ≫ snd (SimplicialCategory.sHom X.1 Y.1) (SimplicialCategory.sHom X.2 Y.2))
  refine ⟨lift f g, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using hf.symm
  · simpa only [Category.assoc, lift_snd] using hg.symm

/-- 第一の対象を固定し、第二の対象の全高次の射を積の豊穣圏へ含める。 -/
def simplicialPairRightInclusion {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) (D : Type w) [Category.{u} D] [SimplicialCategory D] :
    EnrichedFunctor SSet.{u} D (SimplicialPairObject C D) where
  obj Y := (X, Y)
  map Y Z := lift (toUnit (SimplicialCategory.sHom Y Z) ≫ eId SSet X) (𝟙 _)
  map_id _Y := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  map_comp _Y _Z _W := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · exact (congrArg (fun k ↦ k.app n ((eId SSet X).app n PUnit.unit))
        (e_id_comp SSet X X)).symm
    · rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
