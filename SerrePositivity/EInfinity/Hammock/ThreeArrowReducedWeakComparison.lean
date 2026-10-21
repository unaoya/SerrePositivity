module

public import SerrePositivity.EInfinity.Hammock.ThreeArrowGraphWeakComparison
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

/-!
# 元の三列から reduced hammock への正規化の弱同値性

概要：元の三列の正規化自身は弱ホモトピー同値となる。
方針：元の三列の標準射と、既存の余極限の縮約同型を合成する。
規約：元の正規化の全単体作用素を保持する。
使われ方：元の Map^h の共通始域から reduced hammock への比較。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma threeArrowNormalization_isWeakHomotopyEquivalence : IsWeakHomotopyEquivalence
    (graphNormalization (weakEquivalences C) X Y Word.threeArrow) := by
  have hi : IsWeakHomotopyEquivalence (reducedColimitIso (weakEquivalences C) X Y).hom :=
    FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have h := (threeArrowGraphInclusion_isWeakHomotopyEquivalence X Y cof).comp hi
  rw [reducedColimitIso_hom_fac] at h
  exact h

end SerrePositivity.EInfinity.Hammock
