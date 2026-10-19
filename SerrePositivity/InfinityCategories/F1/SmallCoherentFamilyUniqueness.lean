module

public import SerrePositivity.InfinityCategories.F1.SmallCoherentPrismUniqueness
public import SerrePositivity.InfinityCategories.F1.CoherentTransformationSpaceCurry
public import SerrePositivity.InfinityCategories.F1.RelativeArrowFamilyRealization

/-!
概要：同じ小さい相対射の族の coherent な実現は族全体で関手同型。
方針：積の底上で二つの表現を比較し変換空間の curry で戻す。
規約：パラメーターの各点で別々に同型を選ばない。
使われ方：写像空間比較の左逆を全変換空間にわたって検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ相対射の族の二つの指定両端の coherent な実現は関手同型。
方針：積の底上の prism の一意性を変換空間の curry でパラメーター全体へ戻す。
規約：全空間とパラメーターが各次数で小さい場合。底の小ささは不要。
使われ方：比較射の復元と元の変換の族の全体での比較。 -/
lemma small_coherentFamily_uniqueness {E F B K : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)] [∀ n, Small.{u} (K.obj n)]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
    (H H' : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ R₀.diagram)
    (h₁ : prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ R₁.diagram)
    (h₀' : prismEndpoint 0 (B ⊗ K) ≫ H' = fst B K ≫ R₀.diagram)
    (h₁' : prismEndpoint 1 (B ⊗ K) ≫ H' = fst B K ≫ R₁.diagram)
    (W W' : (Δ[1] : SSet.{u + 1}) ⊗ (E ⊗ K) ⟶ PointedSpaceInfinity.{u})
    (hw₀ : prismEndpoint 0 (E ⊗ K) ≫ W = fst E K ≫ R₀.pointedMap)
    (hw₁ : prismEndpoint 1 (E ⊗ K) ≫ W = f ≫ R₁.pointedMap)
    (hw₀' : prismEndpoint 0 (E ⊗ K) ≫ W' = fst E K ≫ R₀.pointedMap)
    (hw₁' : prismEndpoint 1 (E ⊗ K) ≫ W' = f ≫ R₁.pointedMap)
    (hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ (p ▷ K)) ≫ H)
    (hwp' : W' ≫ pointedSpaceProjection = (Δ[1] ◁ (p ▷ K)) ≫ H') :
    Nonempty (FunctorIso (coherentTransformationFamilyCurry R₀.diagram R₁.diagram H h₀ h₁)
      (coherentTransformationFamilyCurry R₀.diagram R₁.diagram H' h₀' h₁')) := by
  have : ∀ n, Small.{u} ((E ⊗ K).obj n) := by
    intro n; change Small.{u} (E.obj n × K.obj n); infer_instance
  have : ∀ n, Small.{u} ((F ⊗ K).obj n) := by
    intro n; change Small.{u} (F.obj n × K.obj n); infer_instance
  let f' := lift f (snd E K)
  have hf' := relativeArrowFamily_pair_projection p q f hf
  have hw₁a : prismEndpoint 1 (E ⊗ K) ≫ W = f' ≫ (R₁.tensor K).pointedMap := by
    rw [LeftTransportRepresentation.tensor_pointedMap, ← Category.assoc, lift_fst]
    exact hw₁
  have hw₁b : prismEndpoint 1 (E ⊗ K) ≫ W' = f' ≫ (R₁.tensor K).pointedMap := by
    rw [LeftTransportRepresentation.tensor_pointedMap, ← Category.assoc, lift_fst]
    exact hw₁'
  obtain ⟨e⟩ := small_coherentPrism_uniqueness (p ▷ K) (q ▷ K) f' hf'
    (R₀.tensor K) (R₁.tensor K) H H' h₀ h₁ h₀' h₁' W W'
    (by simpa only [LeftTransportRepresentation.tensor_pointedMap] using hw₀) hw₁a
    (by simpa only [LeftTransportRepresentation.tensor_pointedMap] using hw₀') hw₁b hwp hwp'
  exact ⟨coherentTransformationFamilyIsoOfSpaceIso R₀.diagram R₁.diagram H H' h₀ h₁ h₀' h₁'
    (prismEndpointPair_comp_eq _ _ H h₀ h₁) (prismEndpointPair_comp_eq _ _ H' h₀' h₁') e⟩

end SerrePositivity.InfinityCategories
