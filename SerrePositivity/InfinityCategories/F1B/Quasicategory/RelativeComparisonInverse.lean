module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy
public import SerrePositivity.InfinityCategories.Core.FixedDiagramCylinderIso
public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber

/-!
概要：元の全境界を固定する実比較を、同じ固定図式の中で逆向きにする。
方針：円柱を制限射の fiber へ写し、その中の可逆辺の逆を実現する。
規約：境界定値性を全時刻の等式として保ち、逆辺を全関手圏で選び直さない。
使われ方：c5 の尾部比較の向きを、元の有限図式との貼合せに合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- 元の全境界上で定値な実可逆比較は、同じ固定図式の fiber 内の同型を与える。 -/
lemma fixedDiagramVertexIso_of_relativeHomotopy
    {K T X : SSet.{u}} [Quasicategory X] (j : K ⟶ T) [Mono j]
    (p : K ⟶ X) (f g : T ⟶ X) (hf : j ≫ f = p) (hg : j ≫ g = p)
    (H : SSet.Homotopy f g)
    (hfixed : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p)
    (hi : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    Nonempty (VertexIso (X := vertexFiber ((pre j).app X) (functorVertex p))
      (fixedDiagramVertex j p f hf) (fixedDiagramVertex j p g hg)) := by
  have hF : curry H.h ≫ (pre j).app X = SSet.const (functorVertex p) := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_const_functorVertex]
    exact hfixed
  let a := vertexFiberLift ((pre j).app X) (functorVertex p) (curry H.h) hF
  let e := edgeOfSimplex (SSet.yonedaEquiv a)
  have h₀ : (vertexFiber ((pre j).app X) (functorVertex p)).δ 1
      (SSet.yonedaEquiv a) = fixedDiagramVertex j p f hf := by
    apply Subtype.ext
    change ((ihom T).obj X).δ 1 (SSet.yonedaEquiv (curry H.h)) = functorVertex f
    rw [← functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry, H.h₀]
  have h₁ : (vertexFiber ((pre j).app X) (functorVertex p)).δ 0
      (SSet.yonedaEquiv a) = fixedDiagramVertex j p g hg := by
    apply Subtype.ext
    change ((ihom T).obj X).δ 0 (SSet.yonedaEquiv (curry H.h)) = functorVertex g
    rw [← functorVertex_uncurry_one, Equiv.symm_apply_apply, uncurry_curry, H.h₁]
  have hie : IsInvertibleEdge e := by
    apply (isInvertibleEdge_vertexFiber_iff ((pre j).app X) (functorVertex p) e).2
    exact (isInvertibleEdge_congr (e := functorEdgeOfSimplicialHomotopy H)
      (f := e.map ((truncation 2).map (vertexFiberι ((pre j).app X) (functorVertex p))))
      rfl).mp (functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hi)
  exact ⟨eqToIso (congrArg (fun v ↦ HomotopyCategory.mk v) h₀.symm) ≪≫
    asIso (SSet.Truncated.HomotopyCategory.homMk e) ≪≫
      eqToIso (congrArg (fun v ↦ HomotopyCategory.mk v) h₁)⟩

/-- 元の全境界を全時刻で固定する比較の逆も、同じ全境界を全時刻で固定する。 -/
lemma exists_relativeComparisonInverse
    {K T X : SSet.{u}} [Quasicategory X] (j : K ⟶ T) [Mono j]
    (p : K ⟶ X) (f g : T ⟶ X) (hf : j ≫ f = p) (hg : j ≫ g = p)
    (H : SSet.Homotopy f g)
    (hfixed : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p)
    (hi : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ J : SSet.Homotopy g f,
      (j ▷ (Δ[1] : SSet.{u})) ≫ J.h = fst K Δ[1] ≫ p ∧
      ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge J x).toTruncated := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.fixedDiagramVertexIso_of_relativeHomotopy j p f g hf hg H hfixed hi
  exact exists_relative_homotopy_of_fixedDiagram_vertexIso j p g f hg hf e.symm

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relativeComparisonInverse := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.exists_relativeComparisonInverse

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedDiagramVertexIso_of_relativeHomotopy := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.fixedDiagramVertexIso_of_relativeHomotopy
