module
public import SerrePositivity.KST.SConstruction.ObjectBoundaryTriangle
public import SerrePositivity.KST.SConstruction.ObjectAssemblySimplex
public import SerrePositivity.KST.SConstruction.AssemblyAdjointEvaluation

/-! # 元の object S₁ の辺と対象 loop の照合
概要：境界商内の元の辺と、元の零行 loop 射で作った対象の類を同定する。
方針：円の区間上で評価して両者の元の対角組み立てを回収する。
規約：基本群表示の逆元を保持する。使われ方：S₂ の三辺による cofiber 加法関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- 元の S₁ 頂点の loop は、元の object S₁ の辺を円へ降ろした射を表す。 -/
lemma objectBoundaryEdge_loop (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    (zeroRowLoopComparison 0 X).app _
      (⟨e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
        (X := sConstruction 1 X.carrier) e⟩ : (coreSConstruction 1 X.carrier) _⦋0⦌) =
      PointedMapping.familyVertex
        ((SphereSimplex.equiv ((boundaryKanRealizationFunctor 0).obj X) 1).symm
          (objectBoundaryEdge X e)) := by
  let B := (boundaryKanRealizationFunctor 0).obj X
  let d : (coreSConstruction 1 X.carrier) _⦋0⦌ :=
    ⟨e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
      (X := sConstruction 1 X.carrier) e⟩
  let a : (Δ[0] : SSet.{u}) ⟶ coreSConstruction 1 X.carrier := SSet.yonedaEquiv.symm d
  let t := (SphereSimplex.equiv B 1).symm (objectBoundaryEdge X e)
  have ht : PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ t.right =
      (objectBoundaryEdge X e).map := by
    exact congrArg RelativeMorphism.map ((SphereSimplex.equiv B 1).apply_symm_apply _)
  have hp := loop_interval_precomp B a (zeroRowLoopComparison 0 X)
  have hr : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      coreSConstruction 1 X.carrier) ≫
      uncurry (zeroRowLoopComparison 0 X ≫ PointedObject.basedHomι
        PointedSimplicialSet.circle.{u} B) =
      diagonalAssembly 1 (iteratedSRealizationDiagram 0 X) ≫ iteratedRealizationToKan 0 X :=
    zeroRowLoopComparison_assembly 0 X
  rw [hr] at hp
  have ha : ((Δ[1] : SSet.{u}) ◁ a) =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const d) := by
    dsimp only [a]
    rw [SSet.yonedaEquiv_symm_zero]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  have he := congrArg (fun g => g ≫ iteratedRealizationToKan 0 X)
    (objectToCoreSRealization_simplex X.carrier 1 e)
  let v : (Δ[1] : SSet.{u}) ⊗ coreSConstruction 1 X.carrier ⟶ B.right :=
    diagonalAssembly 1 (iteratedSRealizationDiagram 0 X) ≫ iteratedRealizationToKan 0 X
  have he' : lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const d) ≫ v =
      (objectBoundaryEdge X e).map := he.symm
  have hs : ((Δ[1] : SSet.{u}) ◁ a) ≫ v =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ (objectBoundaryEdge X e).map :=
    (congrArg (fun g => g ≫ v) ha).trans ((Category.assoc _ _ _).trans
      (congrArg (fun g => fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ g) he'))
  have hh : a ≫ zeroRowLoopComparison 0 X = PointedMapping.pointFamily t := by
    apply loop_interval_hom_ext
    refine hp.trans (hs.trans (Eq.symm ?_))
    change _ ≫ uncurry (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry PointedSimplicialSet.circle B
      (fst PointedSimplicialSet.circle.right (Δ[0] : SSet.{u}) ≫ t.right) _ ≫ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, uncurry_curry]
    have hf : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ (Δ[0] : SSet.{u})) ≫
        fst PointedSimplicialSet.circle.{u}.right (Δ[0] : SSet.{u}) =
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        PointedObject.cofiberQuotient (boundary.{u} 1).ι := whiskerRight_fst _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ t.right) hf).trans ((Category.assoc _ _ _).trans
        (congrArg (fun g => fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ g) ht)))
  have hv := congrArg SSet.yonedaEquiv hh
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  exact hv

end SerrePositivity.KST.SConstruction
