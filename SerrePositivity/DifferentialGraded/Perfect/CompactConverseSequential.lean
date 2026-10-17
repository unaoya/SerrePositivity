module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseResolutionStages

/-! # 可算余極限の 1-shift による cokernel 表示

三角圏での telescope と、標準 dg 解像度の実際の余極限を比較するための表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive

section
variable {C : Type v} [Category.{w} C] [Preadditive C]
    (F : ℕ ⥤ C) [HasCoproduct (fun n : ULift.{u} ℕ => F.obj n.down)]

abbrev sequentialCoproductFamily (n : ULift.{u} ℕ) := F.obj n.down

def sequentialCoproductShift : (∐ sequentialCoproductFamily.{u} F) ⟶
    ∐ sequentialCoproductFamily.{u} F :=
  Sigma.desc (fun n => F.map (homOfLE (Nat.le_succ n.down)) ≫
    Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n.down + 1⟩)

def sequentialCoproductMap : (∐ sequentialCoproductFamily.{u} F) ⟶
    ∐ sequentialCoproductFamily.{u} F := 𝟙 _ - sequentialCoproductShift.{u} F

def sequentialCoproductProjection (n : ℕ) :
    (∐ sequentialCoproductFamily.{u} F) ⟶ F.obj n :=
  Sigma.desc (Pi.single ⟨n⟩ (𝟙 (F.obj n)))

lemma sequentialCoproductShift_projection_zero :
    sequentialCoproductShift.{u} F ≫ sequentialCoproductProjection.{u} F 0 = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc]

lemma sequentialCoproductShift_projection_succ (n : ℕ) :
    sequentialCoproductShift.{u} F ≫ sequentialCoproductProjection.{u} F (n + 1) =
      sequentialCoproductProjection.{u} F n ≫ F.map (homOfLE (Nat.le_succ n)) := by
  apply Sigma.hom_ext
  intro ⟨i⟩
  by_cases h : i = n
  · subst i
    simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc]
  · simp [sequentialCoproductShift, sequentialCoproductProjection, Category.assoc, h]

def sequentialCoproductDesc (s : Cocone F) : (∐ sequentialCoproductFamily.{u} F) ⟶ s.pt :=
  Sigma.desc (fun n => s.ι.app n.down)

lemma sequentialCoproductMap_desc (s : Cocone F) :
    sequentialCoproductMap.{u} F ≫ sequentialCoproductDesc.{u} F s = 0 := by
  apply Sigma.hom_ext
  intro n
  simp only [sequentialCoproductMap, sequentialCoproductShift, sequentialCoproductDesc,
    comp_sub, sub_comp, Category.id_comp, Category.assoc, Sigma.ι_comp_desc,
    Sigma.ι_comp_desc_assoc, s.w, sub_self, comp_zero]

/-- cokernel への射から元の列の cocone を復元する。 -/
def sequentialCoproductCoconeOfZero {Z : C} (f : (∐ sequentialCoproductFamily.{u} F) ⟶ Z)
    (hf : sequentialCoproductMap.{u} F ≫ f = 0) : Cocone F where
  pt := Z
  ι := NatTrans.ofSequence
    (fun n => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f) (by
      intro n
      have h := congrArg (fun k => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ k) hf
      have he : Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f =
          F.map (homOfLE (Nat.le_succ n)) ≫
            Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n + 1⟩ ≫ f := by
        simpa only [sequentialCoproductMap, sequentialCoproductShift, comp_sub, sub_comp,
          Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
          comp_zero, sub_eq_zero] using h
      change F.map (homOfLE (Nat.le_succ n)) ≫
        (Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n + 1⟩ ≫ f) =
          (Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ f) ≫ 𝟙 Z
      rw [Category.comp_id]
      exact he.symm)

def sequentialCoproductCokernel (s : Cocone F) (hs : IsColimit s) :
    IsColimit (CokernelCofork.ofπ (sequentialCoproductDesc.{u} F s)
      (sequentialCoproductMap_desc.{u} F s)) :=
  Cofork.IsColimit.mk _
    (fun c => hs.desc (sequentialCoproductCoconeOfZero.{u} F c.π (CokernelCofork.condition c)))
    (by
      intro c
      apply Sigma.hom_ext
      intro n
      simpa only [Cofork.π_ofπ, sequentialCoproductDesc, Sigma.ι_comp_desc_assoc,
        sequentialCoproductCoconeOfZero, NatTrans.ofSequence_app] using
        hs.fac (sequentialCoproductCoconeOfZero.{u} F c.π (CokernelCofork.condition c)) n.down)
    (by
      intro c m hm
      apply hs.hom_ext
      intro n
      have h := congrArg (fun k => Sigma.ι (sequentialCoproductFamily.{u} F) ⟨n⟩ ≫ k) hm
      have hf := hs.fac (sequentialCoproductCoconeOfZero.{u} F c.π
        (CokernelCofork.condition c)) n
      simpa only [Cofork.π_ofπ, sequentialCoproductDesc, Sigma.ι_comp_desc_assoc,
        sequentialCoproductCoconeOfZero, NatTrans.ofSequence_app] using h.trans hf.symm)

/-- 加法関手に対する 1-shift の標準余積比較の可換性。 -/
lemma sequentialCoproductMap_sigmaComparison {B : Type*} [Category* B] [Preadditive B]
    (G : C ⥤ B) [G.Additive]
    [HasColimitsOfShape (Discrete (ULift.{u} ℕ)) B] :
    sequentialCoproductMap.{u} (F ⋙ G) ≫
      sigmaComparison G (sequentialCoproductFamily.{u} F) =
        sigmaComparison G (sequentialCoproductFamily.{u} F) ≫
          G.map (sequentialCoproductMap.{u} F) := by
  have hι (n : ULift.{u} ℕ) : Sigma.ι (sequentialCoproductFamily.{u} (F ⋙ G)) n ≫
      sigmaComparison G (sequentialCoproductFamily.{u} F) =
        G.map (Sigma.ι (sequentialCoproductFamily.{u} F) n) := by
    convert ι_comp_sigmaComparison G (sequentialCoproductFamily.{u} F) n using 1 <;> rfl
  apply Sigma.hom_ext
  intro n
  simp only [sequentialCoproductMap, sequentialCoproductShift, comp_sub, sub_comp,
    Category.comp_id, Category.id_comp, Category.assoc, Sigma.ι_comp_desc_assoc,
    hι, reassoc_of% hι, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.comp_map]
  rw [← G.map_comp, ← G.map_comp]
  rw [Sigma.ι_comp_desc]

end

variable (A : Type u) [CommRing A]

/-- ModuleCat の可算 1-shift は単射。遷移射の単射性は不要。 -/
lemma sequentialCoproductMap_moduleCat_injective (F : ℕ ⥤ ModuleCat.{u} A) :
    Function.Injective (sequentialCoproductMap.{u} F) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  have he : z = sequentialCoproductShift.{u} F z := by
    change z - sequentialCoproductShift.{u} F z = 0 at hz
    exact sub_eq_zero.mp hz
  have hp (n : ℕ) : sequentialCoproductProjection.{u} F n z = 0 := by
    induction n with
    | zero =>
      have h := congrArg (fun k => k z) (sequentialCoproductShift_projection_zero.{u} F)
      change sequentialCoproductProjection.{u} F 0 (sequentialCoproductShift.{u} F z) = 0 at h
      exact (congrArg (sequentialCoproductProjection.{u} F 0) he).trans h
    | succ n ih =>
      have h := congrArg (fun k => k z) (sequentialCoproductShift_projection_succ.{u} F n)
      change sequentialCoproductProjection.{u} F (n + 1) (sequentialCoproductShift.{u} F z) =
        F.map (homOfLE (Nat.le_succ n)) (sequentialCoproductProjection.{u} F n z) at h
      rw [ih, map_zero] at h
      exact (congrArg (sequentialCoproductProjection.{u} F (n + 1)) he).trans h
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep A (sequentialCoproductFamily.{u} F)
    (Cofan.mk _ (Sigma.ι _)) (coproductIsCoproduct _) z
  have hai (i : ULift.{u} ℕ) (hi : i ∈ t) : a i = 0 := by
    have h := congrArg (sequentialCoproductProjection.{u} F i.down) ha
    rw [map_sum, hp] at h
    rw [Finset.sum_eq_single i] at h
    · simpa [sequentialCoproductProjection, ← ModuleCat.comp_apply] using h
    · intro j _ hji
      have hij : j ≠ (⟨i.down⟩ : ULift.{u} ℕ) := by simpa using hji
      simp [sequentialCoproductProjection, ← ModuleCat.comp_apply, hij]
    · exact fun h => (h hi).elim
  rw [← ha]
  exact Finset.sum_eq_zero (fun i hi => by rw [hai i hi, map_zero])

lemma sequentialCoproductMap_moduleCat_mono (F : ℕ ⥤ ModuleCat.{u} A) :
    Mono (sequentialCoproductMap.{u} F) :=
  (ModuleCat.mono_iff_injective _).2 (sequentialCoproductMap_moduleCat_injective A F)

lemma sequentialCoproductMap_mono_of_moduleCat_functor
    {C : Type v} [Category.{w} C] [Preadditive C] (F : ℕ ⥤ C)
    [HasCoproduct (sequentialCoproductFamily.{u} F)]
    (G : C ⥤ ModuleCat.{u} A) [G.Additive]
    [PreservesColimit (Discrete.functor (sequentialCoproductFamily.{u} F)) G] :
    Mono (G.map (sequentialCoproductMap.{u} F)) := by
  have : Mono (sequentialCoproductMap.{u} (F ⋙ G)) :=
    sequentialCoproductMap_moduleCat_mono A _
  apply (mono_comp_iff_of_isIso (sigmaComparison G (sequentialCoproductFamily.{u} F)) _).1
  rw [← sequentialCoproductMap_sigmaComparison]
  infer_instance

end SerrePositivity.DifferentialGraded
