module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
/-!
概要：対象条件を保つ実 dg 関手を二つの充満 dg 部分圏へ制限する。
方針：元の Hom 鎖写像と全法則をそのまま保持する。
規約：対象ごとの関手の選択を行わない。使われ方：β5 の射影的模型上の tensor 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w)
variable [DGCategory R D] [DGCategory R E]
/-- 対象条件を保つ実 dg 関手の、二つの充満部分圏への制限。 -/
def dgFullFunctorRestriction (F : DGFunctor R D E) (P : D → Prop) (Q : E → Prop)
    (hF : ∀ x, P x → Q (F.obj x)) :
    DGFunctor R (DGFullSubcategory D P) (DGFullSubcategory E Q) where
  obj x := ⟨F.obj x.val, hF x.val x.property⟩
  map x y := F.map x.val y.val
  map_id x := F.map_id x.val
  map_comp x y z := F.map_comp x.val y.val z.val
/-- 部分圏への制限の包含像は、元の同じ dg 関手への包含の合成。 -/
lemma dgFullFunctorRestriction_inclusion (F : DGFunctor R D E) (P : D → Prop) (Q : E → Prop)
    (hF : ∀ x, P x → Q (F.obj x)) :
    (dgFullFunctorRestriction R D E F P Q hF).comp (dgFullSubcategoryInclusion R E Q) =
      (dgFullSubcategoryInclusion R D P).comp F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (F.map x.val y.val ≫ 𝟙 _) ≫ eqToHom _ = 𝟙 _ ≫ F.map x.val y.val
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
omit [DGCategory R E] in
/-- 恒等 dg 関手の制限は、同じ全部分圏の恒等 dg 関手。 -/
lemma dgFullFunctorRestriction_id (P : D → Prop) :
    dgFullFunctorRestriction R D D (DGFunctor.id D) P P (fun _ h => h) =
      DGFunctor.id (DGFullSubcategory D P) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (𝟙 _) ≫ eqToHom _ = 𝟙 _
  simp only [eqToHom_refl, Category.id_comp]
/-- 合成の制限は、元の二つの制限の厳密な合成。 -/
lemma dgFullFunctorRestriction_comp {T : Type w} [DGCategory R T]
    (F : DGFunctor R D E) (G : DGFunctor R E T)
    (P : D → Prop) (Q : E → Prop) (S : T → Prop)
    (hF : ∀ x, P x → Q (F.obj x)) (hG : ∀ y, Q y → S (G.obj y)) :
    dgFullFunctorRestriction R D T (F.comp G) P S (fun x hx => hG _ (hF x hx)) =
      (dgFullFunctorRestriction R D E F P Q hF).comp
        (dgFullFunctorRestriction R E T G Q S hG) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (F.map x.val y.val ≫ G.map _ _) ≫ eqToHom _ = F.map x.val y.val ≫ G.map _ _
  simp only [eqToHom_refl, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
