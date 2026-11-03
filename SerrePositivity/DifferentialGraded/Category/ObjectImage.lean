module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 対象ラベルで指定した dg 圏の充満像

概要：任意の対象族に沿って Hom 複体・単位・合成を引き戻す。
方針：対象ラベルを独立した型に包み、元の dg 構造の法則を継承する。
規約：ラベルの重複を許す。使われ方：β3 の代表加群の同一宇宙での模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory

/-- dg 圏の指定対象族のラベルを対象とする充満像。 -/
structure DGObjectImage {D : Type v} {E : Type w} (f : D → E) where
  label : D

variable (A : Type u) [CommRing A] {D : Type v} {E : Type w} [DGCategory A E] (f : D → E)

/-- 指定された対象族に沿って Hom 複体と豊穣圏の法則を引き戻す。 -/
instance dgObjectImageEnrichment : DGCategory A (DGObjectImage f) :=
  ofHomObjects A _ (fun x y => homObject A E (f x.label) (f y.label))
    (fun x => eId (Complex A) (f x.label))
    (fun x y z => eComp (Complex A) (f x.label) (f y.label) (f z.label))
    (fun x y => EnrichedCategory.id_comp (f x.label) (f y.label))
    (fun x y => EnrichedCategory.comp_id (f x.label) (f y.label))
    (fun w x y z => EnrichedCategory.assoc (f w.label) (f x.label) (f y.label) (f z.label))

/-- ラベル付き充満像から元の dg 圏への評価関手。 -/
def dgObjectImageEvaluation : DGFunctor A (DGObjectImage f) E where
  obj x := f x.label
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

variable {A f} [DGCategory A D]

/-- dg 関手の対象族が定める充満像への関手。 -/
def dgFunctorToObjectImage (F : DGFunctor A D E) : DGFunctor A D (DGObjectImage F.obj) where
  obj x := ⟨x⟩
  map x y := F.map x y
  map_id x := F.map_id x
  map_comp x y z := F.map_comp x y z

/-- 充満像を経由する dg 関手の分解は厳密に元の関手に等しい。 -/
lemma dgFunctorToObjectImage_evaluation (F : DGFunctor A D E) :
    (dgFunctorToObjectImage F).comp (dgObjectImageEvaluation A F.obj) = F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]

/-- 充満像への関手は対象上全射。 -/
lemma dgFunctorToObjectImage_obj_surjective (F : DGFunctor A D E) :
    Function.Surjective (dgFunctorToObjectImage F).obj := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

end SerrePositivity.InfinityCategories
