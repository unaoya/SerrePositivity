module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleEncoderParameterEquality
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleIntervalFaithfulness
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleSplitReduction

/-!
概要：各次数が一点のパラメーターでは、実 coherent encoder は単射である。
方針：各 K 頂点上の全高次区間を全 K 区間へ戻し、普遍区間の単射性を使う。
規約：一般の K の単射性は結論しない。
使われ方：厳密切断の単射性還元を、点パラメーターで実際に検証する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleCoherentEncoder_mono_of_subsingleton_parameter
    (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    [∀ d, Subsingleton (K.obj d)] (k : K _⦋0⦌)
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z)) :
    Mono (controlledTriangleCoherentEncoder X Y Z K f g a hf hg) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro l l' h
  let Q := controlledTriangleUniversalInterval X Z K (controlledTriangleCompositeFamily X Y Z K f g)
  apply (injective_of_mono ((curry Q).app (Opposite.op ⦋n⦌)))
  apply curry_app_eq_of_parameter_eq Q
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left]
  have hv := controlledTriangleCoherentEncoder_interval_at_vertex_eq X Y Z K f g a hf hg l l' h k
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨b, s, t⟩
  have hs : s = (SSet.const k : (Δ[1] : SSet.{u + 1}) ⊗ Δ[n] ⟶ K).app
      (Opposite.op ⦋d⦌) (b, t) := Subsingleton.elim _ _
  subst s
  let w : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[n]) _⦋d⦌ := (b, t)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hv (Opposite.op ⦋d⦌)) w
  exact he

/-- 各次数が一点の K では、実 encoder に元の native Hom を保つ厳密左逆がある。 -/
lemma controlledTriangleCoherentEncoder_split_of_subsingleton_parameter
    (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    [∀ d, Subsingleton (K.obj d)] (k : K _⦋0⦌)
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z)) :
    ∃ read : controlledTriangleFamilySpace K a ⟶ controlledTriangleLongHomSpace X Z K
        (controlledTriangleCompositeFamily X Y Z K f g),
      controlledTriangleCoherentEncoder X Y Z K f g a hf hg ≫ read = 𝟙 _ ∧
        ∀ t, controlledTriangleNativeRelation X Z K (controlledTriangleCompositeFamily X Y Z K f g)
          a (read.app (Opposite.op ⦋0⦌) t) t := by
  letI := controlledTriangleCoherentEncoder_mono_of_subsingleton_parameter X Y Z K k f g a hf hg
  exact controlledTriangleSplit_of_mono_encoder X Y Z K f g a hf hg _
    (controlledTriangleCoherentEncoder_native X Y Z K f g a hf hg)

end SerrePositivity.InfinityCategories
