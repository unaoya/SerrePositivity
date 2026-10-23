module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationFamilyWitness
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorParameterizedPrismNaturality

/-!
概要：一般の表現間の相対射の実現をパラメーターで制限する。
方針：同じ制限射を prism の三条件へ同時に前合成する。
規約：相対射や変換の族を別々に選び直さない。
使われ方：普遍的な写像空間の族を任意の入力族へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：実現の証拠は任意のパラメーター制限を厳密に保つ。
方針：始点・終点・底に同じ制限射を前合成する。
規約：制限射の単射性や同値性を要求しない。
使われ方：写像空間全体の比較を各族へ制限する。 -/
def TransportRepresentationFamilyWitness.comp {E F B K L : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [LeftFibration p] [LeftFibration q]
    {R : LeftTransportRepresentation p} {S : LeftTransportRepresentation q}
    {t : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (w : TransportRepresentationFamilyWitness R S t f) (i : L ⟶ K) :
    TransportRepresentationFamilyWitness R S (i ≫ t) ((E ◁ i) ≫ f) where
  prism := ((Δ[1] ⊗ E) ◁ i) ≫ w.prism
  source := by
    rw [← Category.assoc, prismEndpoint_parameter_naturality, Category.assoc, w.source,
      ← Category.assoc, whiskerLeft_fst]
  target := by
    rw [← Category.assoc, prismEndpoint_parameter_naturality, Category.assoc, w.target,
      ← Category.assoc]
  projection := by
    rw [Category.assoc, w.projection, ← Category.assoc]
    have hn : ((Δ[1] ⊗ E) ◁ i) ≫ ((Δ[1] ◁ p) ▷ K) =
        ((Δ[1] ◁ p) ▷ L) ≫ ((Δ[1] ⊗ B) ◁ i) := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc, ← functorParameterizedPrism_parameter,
      ← intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories
