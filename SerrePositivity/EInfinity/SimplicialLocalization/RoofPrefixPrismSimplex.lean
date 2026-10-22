module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismCompatibility
public import SerrePositivity.InfinityCategories.F1.CoherentCompositionPrism

/-!
# native roof の元の混合 coherent 単体

概要：元の前面と最後 Hom を全豊穣関手へ組み、同じ終点上の錐単体へ送る。
方針：検証済みの全合成式と豊穣単位則を使う。
規約：任意の時間単体・元の全 path・元の Kan Hom を保持する。
使われ方：native roof 全三角形の slice prism の各単体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def mixedDiagram {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 2))))
      (KanHammockCategory C) :=
  FrameHom.CoherentRightCone.diagram (frontDiagram C U p Γ t)
    ((kanHammockSourceFunctor C).obj Y) (lastHom C U p hp σ hU Γ t)
    (lastHom_comp C U p hp σ hU Γ t)

def simplex {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve C) _⦋n + 1⦌ := mixedDiagram C U p hp σ hU Γ t

lemma simplex_target {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve C).map (PinchedHom.lastVertex n).op (simplex C U p hp σ hU Γ t) =
      coherentNerveVertex ((kanHammockSourceFunctor C).obj Y) := by
  apply (coherentNerveVertexEquiv (KanHammockCategory C)).symm.injective
  change FrameHom.CoherentRightCone.obj (frontDiagram C U p Γ t)
    ((kanHammockSourceFunctor C).obj Y) (Fin.last (n + 1)) = _
  exact FrameHom.CoherentRightCone.obj_last _ _

def sliceSimplex {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    (sliceOver (SSet.yonedaEquiv.symm
      (coherentNerveVertex ((kanHammockSourceFunctor C).obj Y)))) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm (simplex C U p hp σ hU Γ t), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun z : (kanHammockNerve C) _⦋0⦌ => SSet.yonedaEquiv.symm z)
    (simplex_target C U p hp σ hU Γ t)

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
