module
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-! # 指定対象の一対象endomorphism dg圏

積の順序は主モデルのforward composition、すなわち Hom(E,E)⊗Hom(E,E) → Hom(E,E)。
対象型をEで添字付けし、異なる指定対象の豊穣構造の衝突を避ける。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 指定対象Eのendomorphism dg代数を一対象dg圏として扱うための対象型。 -/
inductive EndomorphismObject (E : D) : Type
  | point
  deriving DecidableEq, Inhabited

instance (E : D) : Unique (EndomorphismObject E) where
  default := .point
  uniq x := by cases x; rfl

/-- 非有界Hom複体と単位・豊穣合成を指定enhancementからそのまま継承する。 -/
instance endomorphismDGCategory (E : D) : DGCategory A (EndomorphismObject E) :=
  ofHomObjects A _ (fun _ _ => homObject A D E E)
    (fun _ => eId (Complex A) E) (fun _ _ _ => eComp (Complex A) E E E)
    (fun _ _ => EnrichedCategory.id_comp E E)
    (fun _ _ => EnrichedCategory.comp_id E E)
    (fun _ _ _ _ => EnrichedCategory.assoc E E E E)

/-- 一対象dg圏から指定enhancementへの全Homを保つ包含。 -/
def endomorphismInclusion (E : D) : DGFunctor A (EndomorphismObject E) D where
  obj _ := E
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 一対象のHomはH⁰や導来Endではなく、元の全次数Hom複体である。 -/
lemma endomorphism_hom (E : D) (x y : EndomorphismObject E) :
    homObject A (EndomorphismObject E) x y = homObject A D E E := rfl

/-- 指定対象をdg関手で送るとendomorphismの間のdg関手を得る。 -/
def endomorphismMap {C : Type*} [DGCategory A C] (F : DGFunctor A D C) (E : D) :
    DGFunctor A (EndomorphismObject E) (EndomorphismObject (F.obj E)) where
  obj _ := .point
  map _ _ := F.map E E
  map_id _ := F.map_id E
  map_comp _ _ _ := F.map_comp E E E

/-- End上の写像と元のdg関手の正方形。 -/
lemma endomorphismMap_comp_inclusion {C : Type*} [DGCategory A C]
    (F : DGFunctor A D C) (E : D) :
    (endomorphismMap A F E).comp (endomorphismInclusion A (F.obj E)) =
      (endomorphismInclusion A E).comp F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, endomorphismMap,
    endomorphismInclusion, Category.comp_id, eqToHom_refl]

end SerrePositivity.DifferentialGraded
