module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonConeDiagram

/-! # 全体への比較 cone は有限長比較 cone の逐次余極限

各次数の cone の二成分と、商 Hom の有限長支持を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma lengthComparisonConeCocone_ι_eval (S : Set D) (z : D) (n : ℕ) (x : D) :
    (moduleEvaluation A D x).map ((lengthComparisonConeCocone A D S z).ι.app n) =
      mappingCone.map
        ((moduleEvaluation A D x).map (lengthModuleTransition A D S z (Nat.zero_le n)))
        ((moduleEvaluation A D x).map (lengthModuleInclusion A D S z 0))
        ((moduleEvaluation A D x).map (𝟙 _))
        ((moduleEvaluation A D x).map (lengthModuleInclusion A D S z n))
        (moduleSquare_eval A D _ _ _ _
          (by rw [lengthModuleTransition_inclusion, Category.id_comp]) x) := by
  change (moduleEvaluation A D x).map (moduleConeMap A D
    (lengthModuleTransition A D S z (Nat.zero_le n)) (lengthModuleInclusion A D S z 0)
      (𝟙 _) (lengthModuleInclusion A D S z n)
      (by rw [lengthModuleTransition_inclusion, Category.id_comp])) = _
  exact moduleConeMap_eval A D _ _ _ _ _ x

lemma lengthComparisonConeCocone_f_injective (S : Set D) (z : D) (n : ℕ)
    (x : D) (i : ℤ) :
    Function.Injective (((moduleEvaluation A D x).map
      ((lengthComparisonConeCocone A D S z).ι.app n)).f i) := by
  rw [lengthComparisonConeCocone_ι_eval]
  apply complexConeMap_f_injective A _ _ _ _ _ i
  · rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    exact fun _ _ h => h
  · rw [lengthModuleInclusion_eval]
    exact Subtype.val_injective

/-- 全体 cone の各要素は、ある有限長比較 cone から来る。 -/
lemma lengthComparisonConeCocone_exists (S : Set D) (z x : D) (i : ℤ)
    (t : ((moduleEvaluation A D x).obj (lengthComparisonConeCocone A D S z).pt).X i) :
    ∃ (n : ℕ) (s : ((moduleEvaluation A D x).obj
      ((lengthComparisonConeDiagram A D S z).obj n)).X i),
      ((moduleEvaluation A D x).map ((lengthComparisonConeCocone A D S z).ι.app n)).f i s = t := by
  let g := (moduleEvaluation A D x).map (lengthModuleInclusion A D S z 0)
  let b : (internalHom A D S x z).X i := (mappingCone.snd g).v i i (add_zero i) t
  obtain ⟨n, hn⟩ := exists_lengthSubmodule A D S x z i b
  let f := (moduleEvaluation A D x).map (lengthModuleTransition A D S z (Nat.zero_le n))
  refine ⟨n, complexConeElementMk A f i ((mappingCone.fst g).val.v i (i + 1) rfl t)
    ⟨b, hn⟩, ?_⟩
  let a := (moduleEvaluation A D x).map
    (𝟙 (ForgetEnrichment.of (Complex A) (lengthModule A D S z 0)))
  let c := (moduleEvaluation A D x).map (lengthModuleInclusion A D S z n)
  have hcomm : f ≫ c = a ≫ g := moduleSquare_eval A D _ _ _ _
    (by rw [lengthModuleTransition_inclusion, Category.id_comp]) x
  have hm := complexConeMap_elementMk A f g a c hcomm i
    ((mappingCone.fst g).val.v i (i + 1) rfl t) ⟨b, hn⟩
  have ha : a.f (i + 1) ((mappingCone.fst g).val.v i (i + 1) rfl t) =
      (mappingCone.fst g).val.v i (i + 1) rfl t := by
    dsimp only [a]
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  have hc : c.f i ⟨b, hn⟩ = b := by
    dsimp only [c]
    rw [lengthModuleInclusion_eval]
    rfl
  have he : complexConeElementMk A g i
      (a.f (i + 1) ((mappingCone.fst g).val.v i (i + 1) rfl t)) (c.f i ⟨b, hn⟩) = t := by
    rw [ha, hc]
    exact complexConeElementMk_eta A g i t
  rw [lengthComparisonConeCocone_ι_eval]
  exact hm.trans he

def lengthComparisonConeCocone_degree_isColimit (S : Set D) (z x : D) (i : ℤ) :
    IsColimit
      ((moduleEvaluation A D x ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
        (lengthComparisonConeCocone A D S z)) := by
  have : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (forget (ModuleCat.{u} A))
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro t
    obtain ⟨n, s, hs⟩ := lengthComparisonConeCocone_exists A D S z x i t
    exact ⟨n, s, hs.symm⟩
  · intro n t s h
    have he := lengthComparisonConeCocone_f_injective A D S z n x i h
    exact ⟨n, 𝟙 n, by rw [he]⟩

def lengthComparisonConeCocone_eval_isColimit (S : Set D) (z x : D) :
    IsColimit ((moduleEvaluation A D x).mapCocone (lengthComparisonConeCocone A D S z)) :=
  HomologicalComplex.isColimitOfEval _ _
    (lengthComparisonConeCocone_degree_isColimit A D S z x)

/-- 加群圏内での比較 cone の厳密な余極限性。 -/
def lengthComparisonConeCocone_isColimit (S : Set D) (z : D) :
    IsColimit (lengthComparisonConeCocone A D S z) :=
  moduleIsColimitOfEvaluations A D _ (lengthComparisonConeCocone_eval_isColimit A D S z)

end SerrePositivity.DifferentialGraded.DGQuotient
