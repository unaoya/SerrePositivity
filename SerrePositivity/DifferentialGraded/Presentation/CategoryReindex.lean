module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryData
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：任意の小さい対象型上の提示データを、κ の指定初期区間へ再添字する。
方針：対象の同値で Hom 提示・単位・合成・三法則をそのまま引き戻す。
規約：対象の同値を入力に保持し、評価の全 Hom 作用は恒等にする。
使われ方：非連結和にまとめた出発提示を元の小さいコード型へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)

namespace DGCategoryPresentationData

def reindex : DGCategoryPresentationCode R κ where
  ordinal := a
  hom x y := c.hom (e x) (e y)
  unit x := c.unit (e x)
  comp x y z := c.comp (e x) (e y) (e z)
  left x y := c.left (e x) (e y)
  right x y := c.right (e x) (e y)
  assoc w x y z := c.assoc (e w) (e x) (e y) (e z)

def reindexEvaluation :
    letI := c.enrichment R κ.ord.ToType X
    DGFunctor R ((reindex R κ X c a e).Objects R κ) X := by
  letI := c.enrichment R κ.ord.ToType X
  exact {
    obj := e
    map _ _ := 𝟙 _
    map_id _ := Category.comp_id _
    map_comp _ _ _ := by
      simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl }

lemma reindexEvaluation_obj_surjective :
    letI := c.enrichment R κ.ord.ToType X
    Function.Surjective (reindexEvaluation R κ X c a e).obj := e.surjective

lemma reindexEvaluation_homIso (x y : (reindex R κ X c a e).Objects R κ) :
    letI := c.enrichment R κ.ord.ToType X
    IsIso ((reindexEvaluation R κ X c a e).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
