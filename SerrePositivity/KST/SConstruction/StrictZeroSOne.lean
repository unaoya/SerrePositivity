module
public import SerrePositivity.KST.SConstruction.ZeroFrameProjection
public import SerrePositivity.KST.SConstruction.GappedDegenerateSquares
public import SerrePositivity.KST.SConstruction.ObjectSVertices
public import SerrePositivity.KST.SConstruction.ObjectTriangulatedKZeroRelations

/-! # 同じ零頂点を保つ S₁ 補完
概要：任意の対象を両対角が指定した同一の零頂点となる gapped 図式へ補完する。
方針：Ar[1] の正の第一行を固定し、残る頂点の像を指定して延長する。
規約：零対象との同型だけでなく頂点の厳密等号を保つ。
使われ方：K₀ 比較のホモトピーの端点補正を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Ar[1] の各区間は第一行または対角にある。 -/
lemma arOne_isFrame (a : Ar.{u} 1) : a.down.val.1 = 0 ∨ IsDiagonal a := by
  by_cases h : a.down.val.1 = 0
  · exact Or.inl h
  · right
    change a.down.val.1 = a.down.val.2
    apply Fin.ext
    have hi := a.down.val.1.isLt
    have hj := a.down.val.2.isLt
    have hij := a.down.property
    have hn : a.down.val.1.val ≠ 0 := fun he ↦ h (Fin.ext he)
    change a.down.val.1.val ≤ a.down.val.2.val at hij
    omega

/-- 指定した同じ零頂点を両対角に持ち、中間頂点を厳密に回収する補完。 -/
lemma exists_strictZeroSOneDiagram {C : SSet.{u}} [Quasicategory C]
    (x z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    ∃ F : arNerve 1 ⟶ C, IsGapped F ∧
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide))) = x ∧
      ∀ j : Fin 2, F.app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj j j le_rfl)) = z := by
  classical
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (arNerve.{u} 1)
    (fun v ↦ IsPositiveRow (nerveEquiv v))
  let values : (arNerve.{u} 1) _⦋0⦌ → C _⦋0⦌ := fun v ↦
    if IsPositiveRow (nerveEquiv v) then x else z
  have hd (v : (arNerve.{u} 1) _⦋0⦌) (h : IsDiagonal (nerveEquiv v)) :
      values v = z := by
    exact ite_eq_right (diagonal_not_positiveRow h)
  obtain ⟨F, _, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_with_vertices A (SSet.const x) values (by
    intro v
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change (if IsPositiveRow (nerveEquiv v.val) then x else z) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0
    rw [ite_eq_left hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]) (by
    intro n s hs
    have hn : ¬ ∀ r, IsPositiveRow (s.obj r) := by
      intro h
      apply hs
      intro α
      exact h (α.toOrderHom 0)
    rcases frameChain_diagonal_endpoint s (fun r ↦ arOne_isFrame (s.obj r)) hn with hi | ht
    · rw [hd _ hi]
      exact Or.inl hz.1
    · rw [hd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) ht]
      exact Or.inr hz.2)
  have hdiag (j : Fin 2) : F.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (arObj j j le_rfl)) = z := by
    rw [hv]
    exact hd _ rfl
  refine ⟨F, isGapped_one_of_zero_diagonal F (fun j ↦ (hdiag j).symm ▸ hz), ?_, hdiag⟩
  rw [hv]
  exact ite_eq_left ⟨rfl, by change (0 : Fin 2) < 1; decide⟩

/-- Ar[0] の図式は唯一の頂点での評価で決まる。 -/
lemma arZero_hom_ext {C : SSet.{u}} (F G : arNerve 0 ⟶ C)
    (h : F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (0 : Fin 1) 0 le_rfl)) =
      G.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (0 : Fin 1) 0 le_rfl))) : F = G := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have hs : s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (ComposableArrows.mk₀ (arObj (0 : Fin 1) 0 le_rfl)) n := by
    refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> exact Fin.eq_zero _
  rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, h]

/-- 任意の対象は、両端が同じ元の object S₀ 頂点となる S₁ 辺で表される。 -/
lemma exists_closedObjectSOne {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (x : C _⦋0⦌) : ∃ e : (objectSConstruction C) _⦋1⦌,
      (sOneComparison C).app (Opposite.op ⦋0⦌) e = x ∧
      (objectSConstruction C).δ 0 e = (objectSConstruction C).δ 1 e := by
  obtain ⟨F, hF, hx, hz⟩ := exists_strictZeroSOneDiagram x
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero
  let e := gappedObjectVertex F hF
  refine ⟨e, ?_, ?_⟩
  · rw [sOneComparison_gappedDiagram_vertex, gappedDiagram_gappedObjectVertex]
    exact hx
  · apply gappedDiagram_injective
    change gappedDiagram (((objectSConstruction C).map (SimplexCategory.δ 0).op) e) =
      gappedDiagram (((objectSConstruction C).map (SimplexCategory.δ 1).op) e)
    rw [gappedDiagram_objectS_map, gappedDiagram_objectS_map,
      gappedDiagram_gappedObjectVertex]
    apply arZero_hom_ext
    change F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (1 : Fin 2) 1 le_rfl)) =
      F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (0 : Fin 2) 0 le_rfl))
    exact (hz 1).trans (hz 0).symm

end SerrePositivity.KST.SConstruction
