module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsFree
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FreeMapSplitMono

/-!
# 正規化 Moore 複体の各次数の分裂

概要：単体加群の各次数で分裂する射は正規化後も各次数で分裂する。
方針：元の分裂を Moore 包含と標準射影で挟む。
規約：選んだ次数別 retraction の単体自然性は要求しない。
使われ方：単体集合の単射像の射影 cokernel。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedMooreMap_isSplitMono {X Y : SimplicialObject (ModuleCat A)} (f : X ⟶ Y)
    (hf : ∀ n, IsSplitMono (f.app n)) (n : ℕ) :
    IsSplitMono (((normalizedMooreComplex (ModuleCat A)).map f).f n) := by
  let : IsSplitMono (f.app (Opposite.op ⦋n⦌)) := hf _
  have hi := congrArg (fun φ => φ.f n) ((inclusionOfMooreComplex (ModuleCat A)).naturality f)
  change ((normalizedMooreComplex (ModuleCat A)).map f).f n ≫
    (inclusionOfMooreComplexMap Y).f n =
      (inclusionOfMooreComplexMap X).f n ≫ f.app (Opposite.op ⦋n⦌) at hi
  have hs := congrArg (fun φ => φ.f n) (splitMonoInclusionOfMooreComplexMap X).id
  change (inclusionOfMooreComplexMap X).f n ≫
    (PInftyToNormalizedMooreComplex X).f n = 𝟙 _ at hs
  refine ⟨⟨{
    retraction := (inclusionOfMooreComplexMap Y).f n ≫
      retraction (f.app (Opposite.op ⦋n⦌)) ≫ (PInftyToNormalizedMooreComplex X).f n
    id := ?_ }⟩⟩
  rw [← Category.assoc, hi]
  simpa only [Category.assoc, IsSplitMono.id_assoc] using hs

lemma normalizedChainMap_isSplitMono {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] (n : ℕ) :
    IsSplitMono (((normalizedMooreComplex (ModuleCat A)).map
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f)).f n) := by
  apply _root_.SerrePositivity.ComplexLimits.normalizedMooreMap_isSplitMono A _ _ n
  intro d
  change IsSplitMono ((ModuleCat.free A).map (uliftFunctor.{u, 0}.map (f.app d)))
  apply _root_.SerrePositivity.ComplexLimits.freeMap_isSplitMono A
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

end SerrePositivity.ComplexLimits
