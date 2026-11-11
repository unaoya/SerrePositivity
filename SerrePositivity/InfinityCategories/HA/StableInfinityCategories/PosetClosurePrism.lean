module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveVertexExt
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PrismRetraction

/-!
概要：単調な上昇収縮の prism と両端の厳密な等式。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def posetClosureStep (r : P →o P) (hr : ∀ p, p ≤ r p) : Fin 2 × P →o P where
  toFun x := if x.1 = 0 then x.2 else r x.2
  monotone' := by
    intro a b h
    by_cases ha : a.1 = 0
    · by_cases hb : b.1 = 0
      · simp only [ha, hb]; exact h.2
      · simp only [ha, hb]
        exact h.2.trans (hr _)
    · have hb : b.1 ≠ 0 := by intro hb; have := h.1; omega
      simp only [ha, hb]
      exact r.monotone h.2

def posetClosurePrism (r : P →o P) (hr : ∀ p, p ≤ r p) :
    (Δ[1] : SSet.{u}) ⊗ nerve P ⟶ nerve P where
  app n := ↾fun s ↦
    ((posetClosureStep r hr).comp
      (((stdSimplex.objEquiv s.1).toOrderHom).prod
        (⟨s.2.obj, s.2.monotone⟩ : Fin (n.unop.len + 1) →o P))).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma posetClosurePrism_zero (r : P →o P) (hr : ∀ p, p ≤ r p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve P) ≫ posetClosurePrism r hr = 𝟙 (nerve P) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (0 : Fin 2) = 0 then nerveEquiv v else r (nerveEquiv v)) = _
  rw [ite_eq_left rfl]
  rfl

lemma posetClosurePrism_one (r : P →o P) (hr : ∀ p, p ≤ r p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve P) ≫ posetClosurePrism r hr = nerveMap r.toFunctor := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (1 : Fin 2) = 0 then nerveEquiv v else r (nerveEquiv v)) = _
  rw [ite_eq_right (by decide)]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
