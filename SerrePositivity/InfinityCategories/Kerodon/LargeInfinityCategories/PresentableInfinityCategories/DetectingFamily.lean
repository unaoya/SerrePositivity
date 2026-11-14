module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectedRepresentableGenerators
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRepresentableHomDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PostcompositionIsoEquivalence

/-!
概要：presentable な準圏には、元の pinched 写像空間で同値を検出する小さい対象族がある。
方針：小さい前層反映の表現可能対象を左随伴で移し、同じ射に自然な随伴・Yoneda比較を使う。
規約：添字は Type u、値の圏は SSet.{u+1}。検出性や自然性を追加入力にしない。
使われ方：G14、BS の層化の生成辺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の全 pinched 写像空間の後合成の同値性によって射の可逆性を検出する族。 -/
def IsDetectingFamily {E : SSet.{u + 1}} [Quasicategory E] {ι : Type u}
    (M : ι → E _⦋0⦌) : Prop :=
  ∀ {x y : E _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y),
    IsIso f ↔ ∀ i, IsQCatEquivalence (postcompose (M i) f)

/-- 任意の presentable 準圏には、Type u を添字とする実際の写像空間の検出族が存在する。 -/
theorem exists_detectingFamily {E : SSet.{u + 1}} [Quasicategory E] (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (ι : Type u) (M : ι → E _⦋0⦌), IsDetectingFamily M := by
  obtain ⟨A, hA, L, R, ⟨a⟩, hR, _⟩ := hE.exists_presheafReflection
  letI := hA
  refine ⟨A _⦋0⦌, reflectedRepresentable L, ?_⟩
  intro x y f
  constructor
  · intro hf i
    letI := hf
    exact postcompose_isQCatEquivalence_of_isIso _ f
  · intro hf
    let RF := (hoFunctor.map R).toFunctor
    have hr : IsIso (RF.map f) := by
      apply presheafHom_isIso_of_representable_post
      intro i
      have hn := reflectedRepresentableMapping_naturality a i f
      have hc := (hf i).comp (reflectedRepresentableMapping_isQCatEquivalence a i y)
      exact (reflectedRepresentableMapping_isQCatEquivalence a i x).cancel_left
        (hc.ofFunctorIso hn)
    letI : RF.Full := hR.toHoFullyFaithful.full
    letI : RF.Faithful := hR.toHoFullyFaithful.faithful
    letI := hr
    exact isIso_of_reflects_iso f RF

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
