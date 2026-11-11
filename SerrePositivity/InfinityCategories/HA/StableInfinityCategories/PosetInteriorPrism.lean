module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedInitialHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def posetInteriorStep (r : P →o P) (hr : ∀ p, r p ≤ p) : Fin 2 × P →o P where
  toFun x := if x.1 = 0 then r x.2 else x.2
  monotone' := by
    intro a b h
    by_cases ha : a.1 = 0
    · by_cases hb : b.1 = 0
      · simp only [ha, hb]; exact r.monotone h.2
      · simp only [ha, hb]; exact (hr _).trans h.2
    · have hb : b.1 ≠ 0 := by intro hb; have := h.1; omega
      simp only [ha, hb]
      exact h.2

def posetInteriorPrism (r : P →o P) (hr : ∀ p, r p ≤ p) :
    (Δ[1] : SSet.{u}) ⊗ nerve P ⟶ nerve P where
  app n := ↾fun s ↦
    ((posetInteriorStep r hr).comp
      (((stdSimplex.objEquiv s.1).toOrderHom).prod
        (⟨s.2.obj, s.2.monotone⟩ : Fin (n.unop.len + 1) →o P))).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma posetInteriorPrism_zero (r : P →o P) (hr : ∀ p, r p ≤ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve P) ≫ posetInteriorPrism r hr = nerveMap r.toFunctor := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (0 : Fin 2) = 0 then r (nerveEquiv v) else nerveEquiv v) = _
  rw [ite_eq_left rfl]
  rfl

lemma posetInteriorPrism_one (r : P →o P) (hr : ∀ p, r p ≤ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve P) ≫ posetInteriorPrism r hr = 𝟙 (nerve P) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (1 : Fin 2) = 0 then r (nerveEquiv v) else nerveEquiv v) = _
  rw [ite_eq_right (by decide)]
  rfl

lemma posetInteriorPrism_fixed (T : P → Prop) (r : P →o P)
    (hr : ∀ p, r p ≤ p) (hfix : ∀ p, T p → r p = p) :
    (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι) ≫
      posetInteriorPrism r hr =
      snd (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (stdSimplex.objEquiv v.1).toOrderHom 0 = 0 then r (nerveEquiv v.2.val)
    else nerveEquiv v.2.val) = nerveEquiv v.2.val
  split
  · exact hfix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v.2)
  · rfl

lemma posetInterior_leftAnodyne (T : P → Prop) (r : P →o P)
    (hr : ∀ p, r p ≤ p) (hmem : ∀ p, T (r p)) (hfix : ∀ p, T p → r p = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftAnodyneExtensions_of_fixed_initial_homotopy _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosureRetraction T r hmem) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosureRetraction_section T r hmem hfix)
    (posetInteriorPrism r hr)
  · rw [posetInteriorPrism_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _).symm
  · exact posetInteriorPrism_one r hr
  · exact posetInteriorPrism_fixed T r hr hfix

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
