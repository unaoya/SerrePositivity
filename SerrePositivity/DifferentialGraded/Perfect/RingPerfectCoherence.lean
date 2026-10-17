module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectEquivalence

/-! # 有限射影の閉零冪等分裂と元の比較同値の導来・shift・三角図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance strictPerfectDGComplexHomotopyIsIdempotentComplete :
    IsIdempotentComplete (HomotopyCategory A (StrictPerfectDGComplex A)) :=
  Idempotents.Equivalence.isIdempotentComplete
    (strictPerfectDGComplexHomotopyEquivalence A).symm inferInstance

/-- 閉零射のホモトピー冪等元を、実際の有界有限射影複体と閉零射で分裂する。 -/
lemma strictPerfectDGComplex_homotopyIdempotent_splits
    (X : ClosedCategory A (StrictPerfectDGComplex A)) (p : X ⟶ X)
    (hp : boundaryRelation A (StrictPerfectDGComplex A) (p ≫ p) p) :
    ∃ (Y : ClosedCategory A (StrictPerfectDGComplex A)) (i : Y ⟶ X) (r : X ⟶ Y),
      boundaryRelation A (StrictPerfectDGComplex A) (i ≫ r) (𝟙 Y) ∧
      boundaryRelation A (StrictPerfectDGComplex A) (r ≫ i) p := by
  let Q := toHomotopy A (StrictPerfectDGComplex A)
  have hp' : Q.map p ≫ Q.map p = Q.map p :=
    (Q.map_comp p p).symm.trans ((toHomotopy_map_eq_iff A _ _ _).2 hp)
  obtain ⟨Y, i, r, hir, hri⟩ :=
    IsIdempotentComplete.idempotents_split (Q.obj X) (Q.map p) hp'
  obtain ⟨i', hi⟩ := Q.map_surjective i
  obtain ⟨r', hr⟩ := Q.map_surjective r
  refine ⟨Y.as, i', r', ?_, ?_⟩
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hir, Q.map_id]
    rfl
  · apply (toHomotopy_map_eq_iff A _ _ _).1
    rw [Q.map_comp, hi, hr, hri]

/-- 新しい同値の順関手は元の比較なので、主導来包含との既存の自然同型を保つ。 -/
def ringPerfectHomotopyEquivalenceDerivedIso :
    (ringPerfectHomotopyEquivalence A).functor ⋙
      perfectModuleInclusion A PUnit.{1} Set.univ ≅ perfectHomotopyToDGDerived A :=
  perfectHomotopyToDGPerfectCompInclusion A

instance ringPerfectHomotopyEquivalenceDerivedIsoCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalenceDerivedIso A).hom ℤ :=
  inferInstanceAs
    (NatTrans.CommShift (perfectHomotopyToDGPerfectCompInclusion A).hom ℤ)

/-- 同じ自然同型で三角形の比較図式も可換になる。 -/
def ringPerfectHomotopyEquivalenceTriangleIso :
    (ringPerfectHomotopyEquivalence A).functor.mapTriangle ⋙
      (perfectModuleInclusion A PUnit.{1} Set.univ).mapTriangle ≅
        (perfectHomotopyToDGDerived A).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (ringPerfectHomotopyEquivalenceDerivedIso A)

instance ringPerfectHomotopyEquivalenceUnitCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalence A).unitIso.hom ℤ := inferInstance

instance ringPerfectHomotopyEquivalenceCounitCommShift :
    NatTrans.CommShift (ringPerfectHomotopyEquivalence A).counitIso.hom ℤ := inferInstance

/-- 分裂したretractの二つの等式は、元の主Perf比較の下でも同じ冪等元を与える。 -/
lemma perfectHomotopy_idempotent_splits_comparison (X : PerfectHomotopy A) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (K : Complex A) (hK : strictlyPerfectComplex A K)
      (i : perfectHomotopyObj A K hK ⟶ X) (r : X ⟶ perfectHomotopyObj A K hK),
      i ≫ r = 𝟙 _ ∧ r ≫ i = p ∧
      (perfectHomotopyToDGPerfect A).map i ≫ (perfectHomotopyToDGPerfect A).map r = 𝟙 _ ∧
      (perfectHomotopyToDGPerfect A).map r ≫ (perfectHomotopyToDGPerfect A).map i =
        (perfectHomotopyToDGPerfect A).map p := by
  obtain ⟨K, hK, i, r, hir, hri⟩ := perfectHomotopy_idempotent_splits_complex A X p hp
  refine ⟨K, hK, i, r, hir, hri, ?_, ?_⟩
  · rw [← Functor.map_comp, hir]
    exact (perfectHomotopyToDGPerfect A).map_id _
  · rw [← Functor.map_comp, hri]

end SerrePositivity.DifferentialGraded
