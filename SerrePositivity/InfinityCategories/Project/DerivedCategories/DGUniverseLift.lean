module
public import SerrePositivity.DifferentialGraded.Category.ObjectImage

/-! # dg 圏の対象宇宙の持ち上げ

概要：対象だけを ULift し、全 Hom 複体と dg 構造を元のまま保つ。
方針：対象ラベル付き充満像を用い、上げ下げする dg 関手を明示する。
規約：係数と Hom の宇宙は変えない。使われ方：β3 の表現可能加群への Yoneda の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

/-- 対象宇宙を上げた dg 圏。Hom 複体は元の Hom 複体そのもの。 -/
abbrev DGUniverseLift (D : Type v) := _root_.SerrePositivity.InfinityCategories.DGObjectImage (ULift.down : ULift.{w} D → D)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の対象を上の宇宙の対象ラベルへ送る dg 関手。 -/
def dgUniverseLiftUp : DGFunctor A D (DGUniverseLift.{v, w} D) where
  obj x := ⟨ULift.up x⟩
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 上げた対象ラベルを元の対象へ戻す dg 関手。 -/
def dgUniverseLiftDown : DGFunctor A (DGUniverseLift.{v, w} D) D :=
  _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation A (ULift.down : ULift.{w} D → D)

/-- 対象を上げ下げする合成は元の恒等 dg 関手。 -/
lemma dgUniverseLiftUp_comp_down :
    (dgUniverseLiftUp.{u, v, w} A D).comp (dgUniverseLiftDown A D) = DGFunctor.id D := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftUp, dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]

/-- 対象ラベルを下げ上げする合成も恒等 dg 関手。 -/
lemma dgUniverseLiftDown_comp_up :
    (dgUniverseLiftDown.{u, v, w} A D).comp (dgUniverseLiftUp A D) =
      DGFunctor.id (DGUniverseLift.{v, w} D) := by
  apply EnrichedFunctor.ext (Complex A) (fun x => by cases x; rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftUp, dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, DGFunctor.id, EnrichedFunctor.id_map,
    Category.comp_id, eqToHom_refl]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
