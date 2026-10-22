module

public import SerrePositivity.KST.NonConnective.DGSumFamily
public import SerrePositivity.KST.NonConnective.DGCountableSwindle

/-!
概要：id ⊕ T の実 dg 関手と swindle の全 Hom chain map に関する自然性。
方針：二項直和の両注入と可算直和の各注入へ制限して全次数で照合する。
規約：同じ指定した閉 dg 同型を保持し、自然性を閉零射だけから結論しない。
使われ方：明示の κ-compact dg cone 上の Eilenberg swindle。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の id と実可算直和 dg 関手の二項族。 -/
def dgSwindleSummand (j : WalkingPair) :
    DGFunctor R (ModuleCategory R D) (ModuleCategory R D) where
  obj M := j.casesOn M (dgCountableSumObj R D M)
  map M N := by
    cases j
    · exact 𝟙 _
    · exact dgCountableSumHom R D M N
  map_id M := by
    cases j
    · exact Category.comp_id _
    · exact dgCountableSumHom_id R D M
  map_comp M N P := by
    cases j
    · simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    · exact dgCountableSumHom_comp R D M N P

/-- id ⊕ T の全 Hom 作用を、実二項直和の豊穣普遍性から作る。 -/
def dgSwindleSourceFunctor : DGFunctor R (ModuleCategory R D) (ModuleCategory R D) :=
  dgSumFamilyFunctor R D (dgSwindleSummand R D)

/-- この dg 直和の対象は、指定した元の二項直和そのもの。 -/
lemma dgSwindleSourceFunctor_obj (M : ModuleCategory R D) :
    (dgSwindleSourceFunctor R D).obj M = (M ⨿ dgCountableSumObj R D M) := rfl

/-- 元の実後続成分射。 -/
abbrev dgSwindleTail (M : ModuleCategory R D) := countableTail (ModuleCategory R D) M

/-- 同じ元の後続成分射は、可算直和の全 Hom 作用と可換。 -/
lemma dgCountableSumHom_tail (M N : ModuleCategory R D) :
    dgCountableSumHom R D M N ≫ eHomWhiskerLeft (Complex R)
      (dgCountableSumObj R D M) (dgSwindleTail R D N) =
    dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
      (dgSwindleTail R D M) (dgCountableSumObj R D N) := by
  apply (moduleCoproductHomIsLimit R D (fun _ : ℕ ↦ M) (dgCountableSumObj R D N)).hom_ext
  intro n
  change (dgCountableSumHom R D M N ≫ eHomWhiskerLeft (Complex R) _
    (dgSwindleTail R D N)) ≫
      eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n.as) _ =
    (dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
      (dgSwindleTail R D M) _) ≫
      eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n.as) _
  rw [Category.assoc, eHom_whisker_exchange, ← Category.assoc,
    dgCountableSumHom_injection, Category.assoc, ← eHomWhiskerLeft_comp]
  rw [← eHomWhiskerRight_comp]
  have hM : dgCountableSumInjection R D M n.as ≫ dgSwindleTail R D M =
      dgCountableSumInjection R D M (n.as + 1) := Sigma.ι_comp_desc _ _
  have hN : dgCountableSumInjection R D N n.as ≫ dgSwindleTail R D N =
      dgCountableSumInjection R D N (n.as + 1) := Sigma.ι_comp_desc _ _
  rw [hM, hN, dgCountableSumHom_injection]

/-- 同じ指定した swindle 同型の全 Hom chain map 上での自然性。 -/
theorem dgSwindleHom_enriched_naturality (M N : ModuleCategory R D) :
    (dgSwindleSourceFunctor R D).map M N ≫ eHomWhiskerLeft (Complex R)
      ((dgSwindleSourceFunctor R D).obj M) (countableSwindleHom (ModuleCategory R D) N) =
    dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
      (countableSwindleHom (ModuleCategory R D) M) (dgCountableSumObj R D N) := by
  apply (moduleCoproductHomIsLimit R D (fun j ↦ (dgSwindleSummand R D j).obj M)
    (dgCountableSumObj R D N)).hom_ext
  intro j
  change ((dgSwindleSourceFunctor R D).map M N ≫ eHomWhiskerLeft (Complex R) _
    (countableSwindleHom (ModuleCategory R D) N)) ≫ eHomWhiskerRight (Complex R)
      (Sigma.ι (fun j ↦ (dgSwindleSummand R D j).obj M) j.as) _ =
    (dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
      (countableSwindleHom (ModuleCategory R D) M) _) ≫ eHomWhiskerRight (Complex R)
      (Sigma.ι (fun j ↦ (dgSwindleSummand R D j).obj M) j.as) _
  rw [Category.assoc, eHom_whisker_exchange, ← Category.assoc]
  change (dgSumFamilyHom R D (dgSwindleSummand R D) M N ≫
      eHomWhiskerRight (Complex R)
        (Sigma.ι (fun j ↦ (dgSwindleSummand R D j).obj M) j.as)
        (dgSumFamilyObj R D (dgSwindleSummand R D) N)) ≫
      eHomWhiskerLeft (Complex R) ((dgSwindleSummand R D j.as).obj M)
        (countableSwindleHom (ModuleCategory R D) N) =
    (dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
      (countableSwindleHom (ModuleCategory R D) M) (dgCountableSumObj R D N)) ≫
      eHomWhiskerRight (Complex R)
        (Sigma.ι (fun j ↦ (dgSwindleSummand R D j).obj M) j.as) (dgCountableSumObj R D N)
  rw [dgSumFamilyHom_injection, Category.assoc, ← eHomWhiskerLeft_comp,
    Category.assoc, ← eHomWhiskerRight_comp]
  rcases j with ⟨j⟩
  cases j with
  | left =>
    change 𝟙 _ ≫ eHomWhiskerLeft (Complex R) M
      (coprod.inl ≫ countableSwindleHom (ModuleCategory R D) N) =
      dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
        (coprod.inl ≫ countableSwindleHom (ModuleCategory R D) M) _
    simp only [countableSwindleHom, coprod.inl_desc, Category.id_comp]
    exact (dgCountableSumHom_injection R D M N 0).symm
  | right =>
    change dgCountableSumHom R D M N ≫ eHomWhiskerLeft (Complex R) _
      (coprod.inr ≫ countableSwindleHom (ModuleCategory R D) N) =
      dgCountableSumHom R D M N ≫ eHomWhiskerRight (Complex R)
        (coprod.inr ≫ countableSwindleHom (ModuleCategory R D) M) _
    simp only [countableSwindleHom, coprod.inr_desc]
    exact dgCountableSumHom_tail R D M N

end SerrePositivity.KST.NonConnective
