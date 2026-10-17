module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetractRangeReduction
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # 一次数の有限射影複体の導来retract

single関手の完全忠実性で冪等元を加群へ戻して分裂し、有限射影加群のsingleを得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_single_finiteProjective (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F] (n : ℤ)
    {X : DerivedCategory (ModuleCat.{u} A)}
    (a : Retract X (DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj F))) :
    ∃ G : ModuleCat.{u} A, Module.Finite A G ∧ Module.Projective A G ∧
      Nonempty (DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj G) ≅ X) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) n
  let p := S.preimage (a.r ≫ a.i)
  have hp : p ≫ p = p := by
    apply S.map_injective
    rw [S.map_comp]
    simp only [p, S.map_preimage, Category.assoc, a.retract_assoc]
  obtain ⟨G, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split F p hp
  let b : Retract G F := ⟨i, r, hir⟩
  have h₁ : S.map i ≫ S.map r = 𝟙 _ := by rw [← S.map_comp, hir, S.map_id]
  have h₂ : S.map r ≫ S.map i = a.r ≫ a.i := by
    rw [← S.map_comp, hri]
    exact S.map_preimage _
  let e : S.obj G ≅ X :=
    { hom := S.map i ≫ a.r
      inv := a.i ≫ S.map r
      hom_inv_id := by
        calc
          _ = S.map i ≫ (a.r ≫ a.i) ≫ S.map r := by simp only [Category.assoc]
          _ = S.map i ≫ (S.map r ≫ S.map i) ≫ S.map r := by rw [h₂]
          _ = _ := by simp only [← Category.assoc, h₁, Category.id_comp]
      inv_hom_id := by
        calc
          _ = a.i ≫ (S.map r ≫ S.map i) ≫ a.r := by simp only [Category.assoc]
          _ = a.i ≫ (a.r ≫ a.i) ≫ a.r := by rw [h₂]
          _ = _ := by simp only [← Category.assoc, a.retract, Category.id_comp] }
  exact ⟨G, finiteModule_of_retract A b,
    Module.Projective.of_split i.hom r.hom (congrArg (fun f => f.hom) hir), ⟨e⟩⟩

lemma ringDerivedRetract_pure_finiteRange (P : Complex A) (hP : strictlyPerfectComplex A P)
    (n : ℤ) [P.IsStrictlyGE n] [P.IsStrictlyLE n]
    {X : DerivedCategory (ModuleCat.{u} A)} (a : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ K.IsStrictlyGE n ∧ K.IsStrictlyLE n ∧
      Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  obtain ⟨F, ⟨e⟩⟩ := P.exists_iso_single n
  let ev : P.X n ≅ F := HomologicalComplex.Hom.isoApp e n ≪≫ singleObjXSelf (.up ℤ) n F
  let := (hP.2 n).1
  let := (hP.2 n).2
  let : Module.Finite A F := Module.Finite.equiv ev.toLinearEquiv
  let : Module.Projective A F := Module.Projective.of_equiv' ev.toLinearEquiv
  obtain ⟨G, hf, hp, ⟨eG⟩⟩ := ringDerivedRetract_single_finiteProjective A F n
    (a.trans (Retract.ofIso (DerivedCategory.Q.mapIso e)))
  let := hf
  let := hp
  exact ⟨_, strictlyPerfectComplex_single A G n, inferInstance, inferInstance, ⟨eG⟩⟩

end SerrePositivity.DifferentialGraded
