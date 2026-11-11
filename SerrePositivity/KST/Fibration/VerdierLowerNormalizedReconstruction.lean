module
public import SerrePositivity.KST.Fibration.VerdierLowerReconstructionBoundary

/-!
概要：元の下側全変形を、同じ長 Hom 読出しの正規化族へ可逆に戻す。
方針：同じ実ホーンと実入力点を Ind-S (9) の正規化仕様へ代入する。
規約：供給命題に条件付き。元 t 自身の厳密対角回収は使わない。
使われ方：K-6 c4 の動く共有対角を正規化側で貼るための実下側の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：実下側族は同じ全 native Hom 読出しと正規化側の厳密対角を持つ族へ可逆比較される。
方針：元の下側全変形を固定ホーン fiber の指定点として同じ再構成へ渡す。
規約：Ind-S (9) に条件付き。切断・読出し合成の比較条項には依存しない。
使われ方：上側の正規化族との共有対角の照合に渡す実下側の長 Hom 族。 -/
theorem verdierLowerNormalizedReconstruction_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    {comparison : ∀ (A : SSet.{u + 1}), (A ⟶ A) → Prop}
    (h9 : zeroMiddleControlledTriangleSupplyWith comparison) :
    let P := SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
    let full : P :=
      { I := Set.univ
        left := Set.mem_univ _
        right := Set.mem_univ _
        left_le := fun k _ => Fin.zero_le k.down
        le_right := fun k _ => Fin.le_last k.down }
    let direct : P :=
      { I := {ULift.up 0, ULift.up 2}
        left := by simp
        right := by simp
        left_le := fun k _ => Fin.zero_le k.down
        le_right := fun k _ => Fin.le_last k.down }
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)))
    let c := verdierLowerReconstructionCompositeFamily d Δ[1]
    ∃ (N : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom Pu).obj H),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (verdierFullSLowerDeformation d).h N) ∧
      ((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N =
        fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d ∧
      (stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ N =
        (Δ[1] ◁ (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
            (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))) ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := Pu) (Y := H)
        (ULift.up (ComposableArrows.mk₀ full)) = c ∧
      ∀ k : (Δ[1] : SSet.{u + 1}) _⦋0⦌,
        let s := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
          ((curry (verdierFullSLowerDeformation d).h).app (Opposite.op ⦋0⦌) k))
        HEq (L.app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  obtain ⟨encode, read, he, hread, hdiag, hnorm, _⟩ := h9
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)) Δ[1]
    (verdierLowerReconstructionFirstFamily d Δ[1])
    (verdierLowerReconstructionLastFamily d Δ[1])
    (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    (verdierLowerReconstructionHorn_first d Δ[1])
    (verdierLowerReconstructionHorn_last d Δ[1])
  let t := verdierLowerReconstructionPoint d
  let ℓ := read.app (Opposite.op ⦋0⦌) t
  let nt := encode.app (Opposite.op ⦋0⦌) ℓ
  let N := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ Δ[1]) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm nt.val
  refine ⟨N, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val, ?_, ?_, hdiag t, ?_, hread t⟩
  · have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (Classical.choice (hnorm t))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre ((horn 2 (1 : Fin 3)).ι ▷ Δ[1])).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)))
    have hN : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex N = nt.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
    exact ⟨hi ≪≫ eqToIso (congrArg HomotopyCategory.mk hN.symm)⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((horn 2 (1 : Fin 3)).ι ▷ Δ[1]) ≫ N) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    change ((pre ((horn 2 (1 : Fin 3)).ι ▷ Δ[1])).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex N) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (fst (Λ[2, 1] : SSet.{u + 1}) Δ[1] ≫ verdierFullSLowerHorn d)
    rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex N = nt.val from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using nt.property
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex _
    have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply ℓ.val
    have hℓ := ℓ.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
    change (((ihom Δ[1]).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)).app (Opposite.op ⦋0⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val)) = _
    exact (congrArg
      ((((ihom Δ[1]).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)).app (Opposite.op ⦋0⦌))) hv).trans hℓ

end SerrePositivity.KST.Fibration
