module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InitialHornProductBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：左脚が同値である span の除算三角形を、全境界を固定して補完できる。
方針：最初の外側ホーンと任意境界の積の充填を、関手圏の基底変更へ移す。
規約：三角形と入力 span は全単体で厳密に比較する。
使われ方：局所化した分母付き span の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def IsEquivalenceSpanVertex {X : SSet.{u}}
    (v : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v)

def equivalenceSpans (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsEquivalenceSpanVertex (X := X)) : SSet.{u})

def equivalenceSpanInclusion (X : SSet.{u}) :
    equivalenceSpans X ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalenceSpanVertex).ι

def equivalenceSpanTriangles (X : SSet.{u}) : SSet.{u} :=
  pullback ((pre (horn 2 0).ι).app X) (equivalenceSpanInclusion X)

def equivalenceSpanTriangleProjection (X : SSet.{u}) :
    equivalenceSpanTriangles X ⟶ equivalenceSpans X := pullback.snd _ _

lemma equivalenceSpan_firstEdge {X : SSet.{u}} [Quasicategory X] {A : SSet.{u}}
    (b : A ⟶ equivalenceSpans X) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((uncurry (b ≫ equivalenceSpanInclusion X)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) x)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (((b ≫ equivalenceSpanInclusion X) ≫ (pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) x) at h
  rw [← curry_uncurry (b ≫ equivalenceSpanInclusion X), curry_pre_app] at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge _)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at h
  have he : horn₂₀.ι₀₁.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0 := by
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    ((uncurry (b ≫ equivalenceSpanInclusion X)).app (Opposite.op ⦋1⦌)
      (horn₂₀.ι₀₁.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) at h
  rw [he] at h
  exact h

instance equivalenceSpanTriangleProjection_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (equivalenceSpanTriangleProjection X) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  let r := ((pre (horn 2 0).ι).app X)
  let A := a ≫ pullback.fst r (equivalenceSpanInclusion X)
  let B := b ≫ equivalenceSpanInclusion X
  have hc : A ≫ r = (boundary n).ι ≫ B := by
    change (a ≫ pullback.fst r (equivalenceSpanInclusion X)) ≫ r = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (a ≫ equivalenceSpanTriangleProjection X) ≫ equivalenceSpanInclusion X = _
    rw [sq.w, Category.assoc]
  have hw : ((horn 2 0).ι ▷ (boundary n : SSet.{u})) ≫ uncurry A =
      ((horn 2 0 : SSet.{u}) ◁ (boundary n).ι) ≫ uncurry B := by
    have h := congrArg uncurry hc
    rw [uncurry_pre_app, uncurry_natural_left] at h
    exact h
  obtain ⟨F, hFb, hFh⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornProduct_fill_boundary 0 n (uncurry A) (uncurry B) hw
    (equivalenceSpan_firstEdge b (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
  have hf : curry F ≫ r = B := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    exact hFh
  have hb : (boundary n).ι ≫ curry F = A := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hFb
  let L := pullback.lift (curry F) b hf
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact hb
    · rw [Category.assoc, pullback.lift_snd]
      exact sq.w.symm
  · exact pullback.lift_snd _ _ _

end SerrePositivity.KST.LocalizingInvariants
