module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：指定された対角のホモトピーに沿って合成三角形を移送し、三次元の証人も保持する。
方針：元の三角形・恒等三角形・指定ホモトピーを Λ³₁ の三面に置いて充填する。
規約：h C の等式から三角形を選び直さない。使われ方：元の比較道を保つ正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X : SSet.{u}} {x y z : X _⦋0⦌}
  {f : X.Edge x y} {g : X.Edge y z} {k k' : X.Edge x z}

structure CompositionDiagonalTransport (s : SSet.Edge.CompStruct f g k)
    (H : SSet.Edge.CompStruct (SSet.Edge.id x) k k') where
  simplex : X _⦋3⦌
  d₀ : X.δ 0 simplex = s.simplex
  d₂ : X.δ 2 simplex = H.simplex
  d₃ : X.δ 3 simplex = (SSet.Edge.CompStruct.idComp f).simplex

lemma compositionDiagonalTransport_nonempty [Quasicategory X]
    (s : SSet.Edge.CompStruct f g k) (H : SSet.Edge.CompStruct (SSet.Edge.id x) k k') :
    Nonempty (CompositionDiagonalTransport s H) := by
  let I := SSet.Edge.CompStruct.idComp f
  obtain ⟨σ, hσ₀, hσ₂, hσ₃⟩ := horn₃₁.exists_desc (SSet.yonedaEquiv.symm s.simplex)
    (SSet.yonedaEquiv.symm H.simplex) (SSet.yonedaEquiv.symm I.simplex)
    (by simp) (by simp) (by simp)
  obtain ⟨T, hT⟩ := Quasicategory.hornFilling (by simp) (by simp) σ
  have h₀ : stdSimplex.δ 0 ≫ T = SSet.yonedaEquiv.symm s.simplex := by simp [← hσ₀, hT]
  have h₂ : stdSimplex.δ 2 ≫ T = SSet.yonedaEquiv.symm H.simplex := by simp [← hσ₂, hT]
  have h₃ : stdSimplex.δ 3 ≫ T = SSet.yonedaEquiv.symm I.simplex := by simp [← hσ₃, hT]
  refine ⟨⟨SSet.yonedaEquiv T, ?_, ?_, ?_⟩⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, h₀, Equiv.apply_symm_apply]
  · rw [← stdSimplex.yonedaEquiv_δ_comp, h₂, Equiv.apply_symm_apply]
  · rw [← stdSimplex.yonedaEquiv_δ_comp, h₃, Equiv.apply_symm_apply]

def compositionDiagonalTransport [Quasicategory X]
    (s : SSet.Edge.CompStruct f g k) (H : SSet.Edge.CompStruct (SSet.Edge.id x) k k') :
    CompositionDiagonalTransport s H := (compositionDiagonalTransport_nonempty s H).some

namespace CompositionDiagonalTransport
variable {s : SSet.Edge.CompStruct f g k}
  {H : SSet.Edge.CompStruct (SSet.Edge.id x) k k'} (w : CompositionDiagonalTransport s H)

def triangle : SSet.Edge.CompStruct f g k' := by
  let T := SSet.yonedaEquiv.symm w.simplex
  have h₀ : stdSimplex.δ 0 ≫ T = SSet.yonedaEquiv.symm s.simplex := by
    apply SSet.yonedaEquiv.injective
    simpa only [T, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using w.d₀
  have h₂ : stdSimplex.δ 2 ≫ T = SSet.yonedaEquiv.symm H.simplex := by
    apply SSet.yonedaEquiv.injective
    simpa only [T, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using w.d₂
  have h₃ : stdSimplex.δ 3 ≫ T =
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp f).simplex := by
    apply SSet.yonedaEquiv.injective
    simpa only [T, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using w.d₃
  dsimp only [T] at h₀ h₂ h₃
  refine SSet.Edge.CompStruct.mk (X.δ 1 w.simplex) ?_ ?_ ?_
  · apply SSet.yonedaEquiv.symm.injective
    simp only [← stdSimplex.δ_comp_yonedaEquiv_symm,
      ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 1) (j := 2) (by simp), h₃]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp f).d₁
  · apply SSet.yonedaEquiv.symm.injective
    simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 0) (j := 0) (by simp), h₀]
  · apply SSet.yonedaEquiv.symm.injective
    simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      dsimp% stdSimplex.δ_comp_δ_self_assoc (i := 1), h₂]

end CompositionDiagonalTransport
end SerrePositivity.KST.LocalizingInvariants
