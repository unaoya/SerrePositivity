module
public import SerrePositivity.DifferentialGraded.Category.FullSubcategory

/-! # 対象の性質を保つdg関手の充満部分圏への制限 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 対象の性質を保つdg関手を充満dg部分圏へ制限する。全Hom射は元の関手と同じである。 -/
def DGFunctor.restrict (F : DGFunctor A D E) (P : D → Prop) (Q : E → Prop)
    (h : ∀ X, P X → Q (F.obj X)) : DGFunctor A (DGFullSubcategory D P) (DGFullSubcategory E Q) where
  obj X := ⟨F.obj X.val, h X.val X.property⟩
  map X Y := F.map X.val Y.val
  map_id X := F.map_id X.val
  map_comp X Y Z := F.map_comp X.val Y.val Z.val

/-- 制限と包含の可換性。抽象的な対象型で証明し、具体的な大きいHom構成を展開しない。 -/
lemma DGFunctor.restrict_comp_inclusion (F : DGFunctor A D E) (P : D → Prop) (Q : E → Prop)
    (h : ∀ X, P X → Q (F.obj X)) :
    DGFunctor.comp (F.restrict P Q h) (dgFullSubcategoryInclusion A E Q) =
      DGFunctor.comp (dgFullSubcategoryInclusion A D P) F := by
  dsimp only [DGFunctor.comp, EnrichedFunctor.comp, DGFunctor.restrict, dgFullSubcategoryInclusion]
  congr 1

end SerrePositivity.DifferentialGraded
