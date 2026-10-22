module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathLift

/-! 元の全 mapping cocone 複体は、恒等写像の同じ path 複体との厳密な引き戻し。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q K : Complex R} (d : P ⟶ Q)

lemma dgGluingCoconePathLift_path (f : K ⟶ mappingCocone (𝟙 Q)) (g : K ⟶ P)
    (h : f ≫ mappingCocone.fst (𝟙 Q) = g ≫ d) :
    dgGluingCoconePathLift d f g h ≫ dgGluingCoconePathMap d = f := by
  apply dgMappingCocone_hom_ext (𝟙 Q)
  · rw [Category.assoc, dgGluingCoconePathMap_fst, ← Category.assoc,
      dgGluingCoconePathLift_fst]
    exact h.symm
  · apply Cochain.ext
    intro n k hnk
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      HomologicalComplex.comp_f, dgGluingCoconePathMap]
    rw [Category.assoc, complexMappingCoconeMap_f_snd_v,
      ← Category.assoc, HomologicalComplex.id_f, Category.comp_id]
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
      Cochain.congr_v (dgGluingCoconePathLift_snd d f g h) n k hnk

lemma dgGluingCoconePath_hom_ext (f g : K ⟶ mappingCocone d)
    (hp : f ≫ dgGluingCoconePathMap d = g ≫ dgGluingCoconePathMap d)
    (ht : f ≫ mappingCocone.fst d = g ≫ mappingCocone.fst d) : f = g := by
  apply dgMappingCocone_hom_ext d f g ht
  apply Cochain.ext
  intro n k hnk
  have he := congrArg (fun m => m.f n ≫ (mappingCocone.snd (𝟙 Q)).v n k hnk) hp
  simp only [HomologicalComplex.comp_f, Category.assoc, dgGluingCoconePathMap,
    complexMappingCoconeMap_f_snd_v, HomologicalComplex.id_f, Category.comp_id] at he
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using he

def dgGluingCoconePathPullbackCone : PullbackCone (mappingCocone.fst (𝟙 Q)) d :=
  PullbackCone.mk (dgGluingCoconePathMap d) (mappingCocone.fst d)
    (dgGluingCoconePathMap_fst d)

def dgGluingCoconePathPullbackCone_isLimit : IsLimit (dgGluingCoconePathPullbackCone d) :=
  PullbackCone.IsLimit.mk _
    (fun s => dgGluingCoconePathLift d s.fst s.snd s.condition)
    (fun s => dgGluingCoconePathLift_path d s.fst s.snd s.condition)
    (fun s => dgGluingCoconePathLift_fst d s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => dgGluingCoconePath_hom_ext d m _
      (hm₁.trans (dgGluingCoconePathLift_path d s.fst s.snd s.condition).symm)
      (hm₂.trans (dgGluingCoconePathLift_fst d s.fst s.snd s.condition).symm))

lemma dgGluingCoconePath_isPullback :
    IsPullback (dgGluingCoconePathMap d) (mappingCocone.fst d)
      (mappingCocone.fst (𝟙 Q)) d :=
  ⟨⟨dgGluingCoconePathMap_fst d⟩, ⟨dgGluingCoconePathPullbackCone_isLimit d⟩⟩

end SerrePositivity.InfinityCategories
