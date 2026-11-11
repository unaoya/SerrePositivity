module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosurePrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeNerve

/-!
概要：全部分複体を固定する順序収縮から right anodyne 性を得る。
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

def posetClosureRetraction (T : P → Prop) (r : P →o P) (hmem : ∀ p, T (r p)) :
    nerve P ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v ↦ T (nerveEquiv v)) (nerveMap r.toFunctor)
    (fun v ↦ hmem (nerveEquiv v))

lemma posetClosureRetraction_section (T : P → Prop) (r : P →o P)
    (hmem : ∀ p, T (r p)) (hfix : ∀ p, T p → r p = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι ≫
      posetClosureRetraction T r hmem = 𝟙 _ := by
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι).mp
  rw [Category.assoc]
  dsimp only [posetClosureRetraction]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, Category.id_comp]
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  exact hfix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)

lemma posetClosurePrism_fixed (T : P → Prop) (r : P →o P)
    (hr : ∀ p, p ≤ r p) (hfix : ∀ p, T p → r p = p) :
    (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosurePrism r hr =
      snd (Δ[1] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  change (if (stdSimplex.objEquiv v.1).toOrderHom 0 = 0 then nerveEquiv v.2.val
    else r (nerveEquiv v.2.val)) = nerveEquiv v.2.val
  split
  · rfl
  · exact hfix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v.2)

lemma posetClosure_rightAnodyne (T : P → Prop) (r : P →o P)
    (hr : ∀ p, p ≤ r p) (hmem : ∀ p, T (r p)) (hfix : ∀ p, T p → r p = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι := by
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stable_rightAnodyneExtensions_of_prism_retraction _
    (posetClosureRetraction T r hmem) (posetClosureRetraction_section T r hmem hfix)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosurePrism r hr) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosurePrism_zero r hr)
  · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetClosurePrism_one]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _).symm
  · exact posetClosurePrism_fixed T r hr hfix

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
