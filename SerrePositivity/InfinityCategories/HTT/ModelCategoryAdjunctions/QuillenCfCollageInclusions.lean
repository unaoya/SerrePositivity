module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage

/-!
概要：両側の元の cf 対象の単体的圏と、同じ Hom を保つ対応圏への二つの豊穣包含。
方針：全充満部分圏の元の Hom の恒等写像を使い、coherent nerve の包含へ移す。
規約：対象・写像空間を選び直さない。使われ方：cf 対応圏の両端 fiber の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section

/-- 元のモデル圏の cf 対象からなる全充満部分圏。 -/
abbrev CofibrantFibrantObjects (C : Type v) [Category.{u} C] [ModelCategory C] :=
  ObjectProperty.FullSubcategory (fun X : C ↦ IsCofibrant X ∧ IsFibrant X)

/-- cf 部分圏の元の対象は、元のモデル構造で cofibrant。 -/
instance cofibrantFibrantObject_isCofibrant {C : Type v} [Category.{u} C] [ModelCategory C]
    (X : CofibrantFibrantObjects C) : IsCofibrant X.obj := X.property.1

/-- 同じ cf 部分圏の元の対象は、元のモデル構造で fibrant。 -/
instance cofibrantFibrantObject_isFibrant {C : Type v} [Category.{u} C] [ModelCategory C]
    (X : CofibrantFibrantObjects C) : IsFibrant X.obj := X.property.2

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [ModelCategory C] [ModelCategory D] [SimplicialCategory C] [SimplicialCategory D]

/-- 元の cf 部分圏の写像空間は、元の固定 SM7 によって Kan。 -/
lemma cofibrantFibrantObjects_sHom_kanComplex
    (S : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
    [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct S.tensor] (X Y : CofibrantFibrantObjects C) :
    KanComplex (SimplicialCategory.sHom X Y) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_kanComplex S X.obj Y.obj

/-- cf 部分圏の元の coherent nerve は quasicategory。 -/
lemma cofibrantFibrantObjects_nerve_quasicategory
    (S : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
    [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct S.tensor] :
    Quasicategory (SimplicialNerve (CofibrantFibrantObjects C)) := by
  have : ∀ X Y : CofibrantFibrantObjects C, KanComplex (SimplicialCategory.sHom X Y) :=
    cofibrantFibrantObjects_sHom_kanComplex S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (CofibrantFibrantObjects C)

/-- 下段の cf 対象を、同じ元の対象・全写像空間で cf 対応圏へ含める。 -/
def quillenCfCollageBottom (R : EnrichedFunctor SSet.{u} D C) :
    EnrichedFunctor SSet.{u} (CofibrantFibrantObjects C) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R) where
  obj X := ⟨(enrichedFunctorCollageBottom R).obj X.obj, X.property⟩
  map X Y := 𝟙 (SimplicialCategory.sHom X.obj Y.obj)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X.obj Y.obj Z.obj ≫ 𝟙 _ =
      (𝟙 (SimplicialCategory.sHom X.obj Y.obj) ⊗ₘ
        𝟙 (SimplicialCategory.sHom Y.obj Z.obj)) ≫ eComp SSet X.obj Y.obj Z.obj
    simp only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp]

/-- 上段も、元の cf 対象と全写像空間をそのまま保つ豊穣包含を持つ。 -/
def quillenCfCollageTop (R : EnrichedFunctor SSet.{u} D C) :
    EnrichedFunctor SSet.{u} (CofibrantFibrantObjects D) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R) where
  obj X := ⟨(enrichedFunctorCollageTop R).obj X.obj, X.property⟩
  map X Y := 𝟙 (SimplicialCategory.sHom X.obj Y.obj)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X.obj Y.obj Z.obj ≫ 𝟙 _ =
      (𝟙 (SimplicialCategory.sHom X.obj Y.obj) ⊗ₘ
        𝟙 (SimplicialCategory.sHom Y.obj Z.obj)) ≫ eComp SSet X.obj Y.obj Z.obj
    simp only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp]

/-- 元の下段 cf ∞ 圏から、同じ cf 対応圏への coherent nerve の包含。 -/
def quillenCfCollageBottomNerve (R : EnrichedFunctor SSet.{u} D C) :
    SimplicialNerve (CofibrantFibrantObjects C) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfCollageBottom R)

/-- 元の上段 cf ∞ 圏からも、同じ cf 対応圏への包含が得られる。 -/
def quillenCfCollageTopNerve (R : EnrichedFunctor SSet.{u} D C) :
    SimplicialNerve (CofibrantFibrantObjects D) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfCollageTop R)

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.7.11" (partial := special) "仮定：固定 SM7 を持つ単体モデル圏の二つの cofibrant-fibrant 対象（Lean が強い：入力数 1 に限る）。結論：二対象間の単体豊穣 Hom は Kan（HA の一入力の場合と一致。多入力 operad 全体の fibrancy は型に含まれない）。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_sHom_kanComplex
