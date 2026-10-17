module
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancementTriangulated
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence

/-! # 実際の射影的perfect dg enhancement内のホモトピー冪等元の分裂

分裂対象は実際の射影的perfect dg加群である。一対象環での有界有限射影複体代表は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance perfectDGHomotopyIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (PerfectDGHomotopyCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (perfectDGModuleHomotopyEquivalence A D S).symm inferInstance

instance smallPerfectDGHomotopyIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (SmallPerfectDGHomotopyCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (smallPerfectDGModuleHomotopyEquivalence A D S).symm inferInstance

lemma perfectDGModule_idempotent_splits (S : Set D)
    (X : PerfectDGHomotopyCategoryOver A D S) (p : X ⟶ X) (hp : p ≫ p = p) :
    ∃ (Y : PerfectDGHomotopyCategoryOver A D S) (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = p :=
  IsIdempotentComplete.idempotents_split X p hp

/-- 閉零射の冪等性を境界関係までで仮定し、実際の閉零分裂射を返す。 -/
lemma perfectDGModule_homotopyIdempotent_splits (S : Set D)
    (X : ClosedCategory A (PerfectDGModuleOver A D S)) (p : X ⟶ X)
    (hp : boundaryRelation A (PerfectDGModuleOver A D S) (p ≫ p) p) :
    ∃ (Y : ClosedCategory A (PerfectDGModuleOver A D S)) (i : Y ⟶ X) (r : X ⟶ Y),
      boundaryRelation A (PerfectDGModuleOver A D S) (i ≫ r) (𝟙 Y) ∧
      boundaryRelation A (PerfectDGModuleOver A D S) (r ≫ i) p := by
  let Q := toHomotopy A (PerfectDGModuleOver A D S)
  have hp' : Q.map p ≫ Q.map p = Q.map p :=
    (Q.map_comp p p).symm.trans ((toHomotopy_map_eq_iff A _ _ _).2 hp)
  obtain ⟨Y, i, r, hir, hri⟩ := perfectDGModule_idempotent_splits A D S (Q.obj X) (Q.map p) hp'
  obtain ⟨i', hi⟩ := Q.map_surjective i
  obtain ⟨r', hr⟩ := Q.map_surjective r
  refine ⟨Y.as, i', r', ?_, ?_⟩
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hir, Q.map_id]
    rfl
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hri]

end SerrePositivity.DifferentialGraded
