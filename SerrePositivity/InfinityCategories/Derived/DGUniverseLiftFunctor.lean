module
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLift

/-! # 対象宇宙を独立に上げた dg 関手

概要：始域と終域の対象宇宙を別々に上げ、元の Hom 写像を保つ dg 関手を作る。
方針：上げた対象ラベルに元の関手を適用し、Hom 複体の写像は変更しない。
規約：係数宇宙を固定。使われ方：Yoneda の nerve を共通宇宙で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r s t q
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w} {T : Type q}
variable [DGCategory A D] [DGCategory A E] [DGCategory A T]

/-- 始域と終域の対象宇宙を独立に上げた dg 関手。 -/
def dgUniverseLiftFunctor (F : DGFunctor A D E) :
    DGFunctor A (DGUniverseLift.{v, r} D) (DGUniverseLift.{w, s} E) where
  obj x := ⟨ULift.up (F.obj x.label.down)⟩
  map x y := F.map x.label.down y.label.down
  map_id x := F.map_id x.label.down
  map_comp x y z := F.map_comp x.label.down y.label.down z.label.down

/-- 宇宙を上げた関手の評価は元の関手と評価の合成。 -/
lemma dgUniverseLiftFunctor_comp_down (F : DGFunctor A D E) :
    (dgUniverseLiftFunctor.{u, v, w, r, s} F).comp (dgUniverseLiftDown A E) =
      (dgUniverseLiftDown A D).comp F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftFunctor, dgUniverseLiftDown,
    dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]

/-- 元の対象を上げることと dg 関手を適用することは可換。 -/
lemma dgUniverseLiftUp_comp_functor (F : DGFunctor A D E) :
    (dgUniverseLiftUp.{u, v, r} A D).comp (dgUniverseLiftFunctor.{u, v, w, r, s} F) =
      F.comp (dgUniverseLiftUp.{u, w, s} A E) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftFunctor, dgUniverseLiftUp,
    Category.id_comp, Category.comp_id, eqToHom_refl]

/-- 対象宇宙の持ち上げは恒等 dg 関手を保つ。 -/
lemma dgUniverseLiftFunctor_id :
    dgUniverseLiftFunctor.{u, v, v, r, r} (DGFunctor.id (A := A) D) =
      DGFunctor.id (DGUniverseLift.{v, r} D) := by
  apply EnrichedFunctor.ext (Complex A) (fun x => by cases x; rfl)
  intro x y
  simp only [dgUniverseLiftFunctor, DGFunctor.id, EnrichedFunctor.id_map,
    Category.comp_id, eqToHom_refl]
  rfl

/-- 対象宇宙の持ち上げは dg 関手の合成を保つ。 -/
lemma dgUniverseLiftFunctor_comp (F : DGFunctor A D E) (G : DGFunctor A E T) :
    dgUniverseLiftFunctor.{u, v, q, r, t} (F.comp G) =
      (dgUniverseLiftFunctor.{u, v, w, r, s} F).comp
        (dgUniverseLiftFunctor.{u, w, q, s, t} G) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [dgUniverseLiftFunctor, EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories
