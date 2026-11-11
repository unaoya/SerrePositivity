module

public import SerrePositivity.KST.Spectra.CoherentSimplexTraces
public import SerrePositivity.KST.Spectra.CoherentPathCompositionFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：始点を重ねた退化二単体の Hom 経路は、元の辺の定値経路である。
方針：二頂点の間の thickening の path の一意性と nerve の前合成を使う。
規約：元の辺の Hom 頂点を保持。使われ方：円評価の三単体の退化面の厳密計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 定値な path の包含列は、その元の零単体の定値写像。 -/
lemma constantPathParameter_eq_const {n : ℕ} {i j : Fin n}
    (P : Path (ULift.up i : ULift.{u} (Fin n)) (ULift.up j)) :
    constantPathParameter P =
      SSet.const ((CategoryTheory.Functor.const (Fin 1)).obj P) := by
  rfl

/-- 始点を重ねる退化は、path 区間を元の辺の一意な path に潰す。 -/
lemma trianglePathInterval_degenerateZero :
    trianglePathInterval.{u} ≫ nerveMap (SimplicialThickening.functorMap
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom.uliftMap
        ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩) =
      constantPathParameter (flaggedPath (fun r : Fin 0 ↦ Fin.elim0 r)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  refine CategoryTheory.Functor.ext (fun _ ↦ ?_) ?_
  · exact @Subsingleton.elim
      (Path (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) (ULift.up 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOnePath_subsingleton _ _) _ _
  · intro i j f
    exact @Subsingleton.elim _ (pathHom_subsingleton _ _) _ _

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 始点退化の Hom 経路は、元の辺を表す Hom の零単体での定値写像。 -/
lemma triangleTrace_degenerateZero (σ : (SimplicialNerve C) _⦋1⦌) :
    triangleTrace ((SimplicialNerve C).σ 0 σ) =
      SSet.const ((σ.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
        ((CategoryTheory.Functor.const (Fin 1)).obj
          (flaggedPath (fun r : Fin 0 ↦ Fin.elim0 r)))) := by
  change trianglePathInterval ≫ (nerveMap (SimplicialThickening.functorMap
    (SimplexCategory.σ (0 : Fin 2)).toOrderHom.uliftMap
      ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up 2⟩) ≫ σ.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩) = _
  rw [← Category.assoc, trianglePathInterval_degenerateZero, constantPathParameter_eq_const,
    SSet.const_comp]
  rfl

/-- 始点退化に等しい二単体の Hom 経路は、元の Hom のある頂点の定値写像。 -/
lemma triangleTrace_constant_of_eq_degenerateZero
    {τ : (SimplicialNerve C) _⦋2⦌} {σ : (SimplicialNerve C) _⦋1⦌}
    (h : τ = (SimplicialNerve C).σ 0 σ) :
    ∃ y, triangleTrace τ = SSet.const y := by
  subst τ
  exact ⟨_, triangleTrace_degenerateZero σ⟩

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
