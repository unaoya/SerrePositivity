module

public import SerrePositivity.CategoryTheory.Enriched.ActionEvaluation

/-!
# 対象ごとの随伴と法則による豊穣化
-/

/-! # 作用の表現性による合成・単位から豊穣圏を構成する -/

@[expose] public section RepresentedMappingEnrichment
universe v₁ v₂ u₁ u₂

noncomputable section

namespace SerrePositivity.RepresentedMappingEnrichment

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V]
  (H : V ⥤ D ⥤ D) (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D) (R : D → D ⥤ V)
  (adj : ∀ E, MappingUnitLaws.parameterFunctor H E ⊣ R E)

/-- 表現性を持つ作用の写像対象。 -/
def hom (E F : D) : V := (R E).obj F

/-- 作用の随伴の余単位による評価。
閉じた V 加群からの構成（`OfAction`）に置き換える予定。使う側が移った後に消す。
-/
def evaluation (E F : D) : (H.obj (hom R E F)).obj E ⟶ F := (adj E).counit.app F

/-- 作用の単位比較を転置した写像対象の単位。
閉じた V 加群からの構成（`OfAction`）に置き換える予定。使う側が移った後に消す。
-/
def unit (E : D) : 𝟙_ V ⟶ hom R E E := (adj E).homEquiv _ E (u.app E).hom

/-- 写像対象の単位の評価の等式。 -/
def unitEvaluationLaw (E : D) : Prop :=
  (H.map (unit H u R adj E)).app E ≫ evaluation H R adj E E = u.hom.app E

/-- 単位の評価は作用の単位比較。 -/
lemma unit_evaluation (E : D) : unitEvaluationLaw H u R adj E :=
  AdjunctionHomLaws.curry_evaluation (adj E) (u.app E).hom

/-- 二回の評価を作用の結同比較へ合成する。 -/
def compositionEvaluation (E F G : D) :
    (H.obj (hom R F G ⊗ hom R E F)).obj E ⟶ G :=
  MappingAssociativity.compositionEvaluation H a (hom R F G) (hom R E F)
    (evaluation H R adj E F) (evaluation H R adj F G)

/-- 二回の評価を転置した合成。 -/
def composition (E F G : D) : hom R F G ⊗ hom R E F ⟶ hom R E G :=
  (adj E).homEquiv _ G (compositionEvaluation H a R adj E F G)

/-- 合成の評価が二回の評価に一致するという法則。 -/
def compositionEvaluationLaw (E F G : D) : Prop :=
  (H.map (composition H a R adj E F G)).app E ≫ evaluation H R adj E G =
    compositionEvaluation H a R adj E F G

/-- 合成の評価は二回の評価に一致する。 -/
lemma composition_evaluation (E F G : D) : compositionEvaluationLaw H a R adj E F G :=
  AdjunctionHomLaws.curry_evaluation (adj E) (compositionEvaluation H a R adj E F G)

/-- 表現性から得た合成の左単位の評価の等式。 -/
def leftUnitEvaluationLaw (E F : D) : Prop :=
  (H.map (unit H u R adj F ⊗ₘ 𝟙 (hom R E F))).app E ≫
    compositionEvaluation H a R adj E F F =
  (H.map (λ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F

/-- 表現性から得た合成の右単位の評価の等式。 -/
def rightUnitEvaluationLaw (E F : D) : Prop :=
  (H.map (𝟙 (hom R E F) ⊗ₘ unit H u R adj E)).app E ≫
    compositionEvaluation H a R adj E E F =
  (H.map (ρ_ (hom R E F)).hom).app E ≫ evaluation H R adj E F

/-- 作用の単位と自然性から写像対象の左単位の評価を計算する。 -/
lemma left_unit_evaluation (E F : D)
    (hn : (H.map (unit H u R adj F ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F F) (hom R E F)).hom.app E =
      (a (𝟙_ V) (hom R E F)).hom.app E ≫
        (H.map (unit H u R adj F)).app ((H.obj (hom R E F)).obj E))
    (he : unitEvaluationLaw H u R adj F)
    (hu : (a (𝟙_ V) (hom R E F)).hom.app E ≫
      u.hom.app ((H.obj (hom R E F)).obj E) = (H.map (λ_ (hom R E F)).hom).app E) :
    leftUnitEvaluationLaw H a u R adj E F :=
  MappingUnitLaws.left_unit_evaluation H u (unit H u R adj F)
    (evaluation H R adj E F) (evaluation H R adj F F)
    ((a (hom R F F) (hom R E F)).hom.app E)
    ((a (𝟙_ V) (hom R E F)).hom.app E) hn he hu

/-- 作用の単位と自然性から写像対象の右単位の評価を計算する。 -/
lemma right_unit_evaluation (E F : D)
    (hn : (H.map (𝟙 (hom R E F) ⊗ₘ unit H u R adj E)).app E ≫
      (a (hom R E F) (hom R E E)).hom.app E =
      (a (hom R E F) (𝟙_ V)).hom.app E ≫
        (H.obj (hom R E F)).map ((H.map (unit H u R adj E)).app E))
    (he : unitEvaluationLaw H u R adj E)
    (hu : (a (hom R E F) (𝟙_ V)).hom.app E ≫
      (H.obj (hom R E F)).map (u.hom.app E) = (H.map (ρ_ (hom R E F)).hom).app E) :
    rightUnitEvaluationLaw H a u R adj E F :=
  MappingUnitLaws.right_unit_evaluation H u (unit H u R adj E)
    (evaluation H R adj E F) (evaluation H R adj E E)
    ((a (hom R E F) (hom R E E)).hom.app E)
    ((a (hom R E F) (𝟙_ V)).hom.app E) hn he hu

/-- 表現性から得た合成の左単位則。 -/
def leftUnitLaw (E F : D) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (adj E) (compositionEvaluation H a R adj E F F)
    (unit H u R adj F ⊗ₘ 𝟙 (hom R E F)) (λ_ (hom R E F)).hom

/-- 表現性から得た合成の右単位則。 -/
def rightUnitLaw (E F : D) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (adj E) (compositionEvaluation H a R adj E E F)
    (𝟙 (hom R E F) ⊗ₘ unit H u R adj E) (ρ_ (hom R E F)).hom

/-- 評価から写像対象の左単位則を得る。 -/
lemma left_unit (E F : D) (h : leftUnitEvaluationLaw H a u R adj E F) :
    leftUnitLaw H a u R adj E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E) (compositionEvaluation H a R adj E F F)
    (unit H u R adj F ⊗ₘ 𝟙 (hom R E F)) (λ_ (hom R E F)).hom h

/-- 評価から写像対象の右単位則を得る。 -/
lemma right_unit (E F : D) (h : rightUnitEvaluationLaw H a u R adj E F) :
    rightUnitLaw H a u R adj E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (adj E) (compositionEvaluation H a R adj E E F)
    (𝟙 (hom R E F) ⊗ₘ unit H u R adj E) (ρ_ (hom R E F)).hom h

/-- 表現性から得た反復合成の評価の一致。 -/
def associativityEvaluationLaw (E F G K : D) : Prop :=
  MappingAssociativity.associativityEvaluationLaw H a
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)

/-- 自然性と五角形から反復合成の評価の一致を得る。 -/
lemma associativity_evaluation (E F G K : D)
    (hl : (H.map (composition H a R adj F G K ⊗ₘ 𝟙 (hom R E F))).app E ≫
      (a (hom R F K) (hom R E F)).hom.app E =
      (a (hom R G K ⊗ hom R F G) (hom R E F)).hom.app E ≫
        (H.map (composition H a R adj F G K)).app ((H.obj (hom R E F)).obj E))
    (hr : (H.map (𝟙 (hom R G K) ⊗ₘ composition H a R adj E F G)).app E ≫
      (a (hom R G K) (hom R E G)).hom.app E =
      (a (hom R G K) (hom R F G ⊗ hom R E F)).hom.app E ≫
        (H.obj (hom R G K)).map ((H.map (composition H a R adj E F G)).app E))
    (hp : (H.map (α_ (hom R G K) (hom R F G) (hom R E F)).hom).app E ≫
      (a (hom R G K) (hom R F G ⊗ hom R E F)).hom.app E ≫
        (H.obj (hom R G K)).map ((a (hom R F G) (hom R E F)).hom.app E) =
      (a (hom R G K ⊗ hom R F G) (hom R E F)).hom.app E ≫
        (a (hom R G K) (hom R F G)).hom.app ((H.obj (hom R E F)).obj E)) :
    associativityEvaluationLaw H a R adj E F G K :=
  MappingAssociativity.associativity_evaluation H a
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj F G) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)
    (composition_evaluation H a R adj F G K) (composition_evaluation H a R adj E F G) hl hr hp

/-- 表現性から得た合成の結合則。 -/
def associativityLaw (E F G K : D) : Prop :=
  MappingAssociativity.representedAssociativityLaw H a (adj E)
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G)

/-- 反復合成の評価の一致から写像対象の結合則を得る。 -/
lemma associativity (E F G K : D) (h : associativityEvaluationLaw H a R adj E F G K) :
    associativityLaw H a R adj E F G K :=
  MappingAssociativity.represented_associativity H a (adj E)
    (composition H a R adj F G K) (composition H a R adj E F G)
    (evaluation H R adj E F) (evaluation H R adj G K)
    (evaluation H R adj F K) (evaluation H R adj E G) h

/-- 通常の射と単位から写像対象への射の同値。
閉じた V 加群からの構成（`OfAction`）に置き換える予定。使う側が移った後に消す。
-/
def arrowEquiv (E F : D) : (E ⟶ F) ≃ (𝟙_ V ⟶ hom R E F) :=
  AdjunctionHomLaws.comparisonHomEquiv (adj E) (u.app E) F

/-- 通常の射に対応する写像対象の点。 -/
def arrow {E F : D} (f : E ⟶ F) : 𝟙_ V ⟶ hom R E F := arrowEquiv H u R adj E F f

/-- 恒等射と写像対象の単位の対応。 -/
def arrowIdentityLaw (E : D) : Prop :=
  AdjunctionHomLaws.comparisonHomIdentityLaw (adj E) (u.app E)

/-- 恒等射は写像対象の単位に対応する。 -/
lemma arrow_identity (E : D) : arrowIdentityLaw H u R adj E :=
  AdjunctionHomLaws.comparisonHomEquiv_id (adj E) (u.app E)

/-- 通常の射の合成と写像対象の点の合成の対応。 -/
def arrowCompositionLaw {E F G : D} (f : E ⟶ F) (g : F ⟶ G) : Prop :=
  MappingArrowComposition.representedArrowCompositionLaw H a u (adj E)
    f g (arrow H u R adj g) (arrow H u R adj f)
    (evaluation H R adj E F) (evaluation H R adj F G)

variable [BraidedCategory V]

/-- 作用の表現性による写像対象の合成を通常の因子順の豊穣圏へまとめる。 -/
@[instance_reducible]
def enrichedCategory (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) : EnrichedCategory V D := by
  apply ReverseComposition.enrichedCategory D (hom R) (unit H u R adj)
    (composition H a R adj) hl hr
  intro W X Y Z
  have h := ha W X Y Z
  change (composition H a R adj X Y Z ⊗ₘ 𝟙 (hom R W X)) ≫
    composition H a R adj W X Z =
    ((α_ (hom R Y Z) (hom R X Y) (hom R W X)).hom ≫
      (𝟙 (hom R Y Z) ⊗ₘ composition H a R adj W X Y)) ≫
        composition H a R adj W Y Z at h
  simpa only [Category.assoc] using h

/-- 豊穣構造の単位は構成した単位。 -/
lemma enrichedCategory_id (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) (E : D) :
    (enrichedCategory H a u R adj hl hr ha).id E = unit H u R adj E := rfl

/-- 豊穣構造の合成は構成した合成の因子を交換したもの。 -/
lemma enrichedCategory_comp (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K) (E F G : D) :
    (enrichedCategory H a u R adj hl hr ha).comp E F G =
      ReverseComposition.reverse (composition H a R adj E F G) := rfl

/-- 表現性による豊穣構造を既存の通常の圏構造と接続する。
閉じた V 加群からの構成（`OfAction`）に置き換える予定。使う側が移った後に消す。
-/
@[instance_reducible]
def ordinaryCategory (hl : ∀ E F, leftUnitLaw H a u R adj E F)
    (hr : ∀ E F, rightUnitLaw H a u R adj E F)
    (ha : ∀ E F G K, associativityLaw H a R adj E F G K)
    (hi : ∀ E, arrowIdentityLaw H u R adj E)
    (hc : ∀ {E F G} (f : E ⟶ F) (g : F ⟶ G), arrowCompositionLaw H a u R adj f g) :
    EnrichedOrdinaryCategory V D where
  toEnrichedCategory := enrichedCategory H a u R adj hl hr ha
  homEquiv := arrowEquiv H u R adj _ _
  homEquiv_id E := hi E
  homEquiv_comp f g := by
    apply Eq.symm
    apply ReverseComposition.points
    exact hc f g

end SerrePositivity.RepresentedMappingEnrichment
end

end RepresentedMappingEnrichment
