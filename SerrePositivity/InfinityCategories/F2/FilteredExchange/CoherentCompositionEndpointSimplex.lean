module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionEndpointWeighted
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionEndpointFirstHom
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionEndpointPositiveHom

/-!
概要：実終点円柱の全三角形は元の反転精密化から作った標準 weighted cone。
方針：対象と全 Hom を比較し、長辺・最初の辺・正頂点・空の逆向きを分ける。
規約：元の全三角形を比較し、精密化の一単体だけの一致で代用しない。
使われ方：実 coslice 終点辺と標準 Hom 比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 実終点円柱の全三角形は元の精密化の反転による標準 weighted cone。 -/
lemma coherentCompositionEndpoint_simplex_weighted
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2)) =
      weightedConeSimplex
        ((Functor.const (Discrete PUnit.{u + 1})).obj (s.obj ⟨ULift.up 2⟩))
        (s.obj ⟨ULift.up 0⟩)
        (weightedNerveConstantDiagram
          (simplicialHomDiagram
            ((Functor.const (Discrete PUnit.{u + 1})).obj (s.obj ⟨ULift.up 2⟩))
            (s.obj ⟨ULift.up 0⟩) ⋙ SSet.opFunctor)
          ⟨PUnit.unit⟩ (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) := by
  let F := (Functor.const (Discrete PUnit.{u + 1})).obj (s.obj ⟨ULift.up 2⟩)
  let x := s.obj ⟨ULift.up 0⟩
  let α := coherentTriangleHomotopy s
  let τ := weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor)
    ⟨PUnit.unit⟩ (SSet.opObjEquiv.symm α)
  let W := coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
    (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))
  let V := weightedConeSimplex F x τ
  change W = V
  refine EnrichedFunctor.ext SSet (fun a ↦ ?_) (fun a b ↦ ?_)
  · rcases a with ⟨⟨a⟩⟩
    fin_cases a <;> rfl
  · rcases a with ⟨⟨a⟩⟩
    rcases b with ⟨⟨b⟩⟩
    simp only [eqToHom_refl, Category.comp_id]
    induction a using Fin.cases <;> induction b using Fin.cases
    case zero.zero =>
      have hw := enrichedFunctor_thickening_self_map W (ULift.up (0 : Fin 3)) rfl
      have hv := enrichedFunctor_thickening_self_map V (ULift.up (0 : Fin 3)) rfl
      simp only [eqToHom_refl, Category.comp_id] at hw hv
      exact hw.trans hv.symm
    case zero.succ b =>
      fin_cases b
      · exact (coherentCompositionEndpoint_hom_zero_one s).trans
          (weightedTriangleFirstHom F x ⟨PUnit.unit⟩ α).symm
      · exact coherentCompositionEndpoint_hom_zero_two_weighted s
    case succ.zero a =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      have h := Path.le (P.obj 0)
      change a.succ ≤ 0 at h
      simp at h
    case succ.succ a b =>
      exact (coherentCompositionEndpoint_hom_positive s a b).trans
        (weightedTrianglePositiveHom x (s.obj ⟨ULift.up 2⟩)
          (SSet.opObjEquiv.symm α) a b).symm

end SerrePositivity.InfinityCategories.F2
