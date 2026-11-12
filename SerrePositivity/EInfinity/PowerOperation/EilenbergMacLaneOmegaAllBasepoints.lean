module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneUnitH0Value
public import SerrePositivity.EInfinity.PowerOperation.ContractibleFiberComparison
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePointedConeFiber
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopTrivialFibration

/-!
# 指定 Γ 構造射の全基点での Ω 条件

DAG XIII §2.2 のスペクトル忘却への前段。元の恒等 cone の固定 fiber を使い、
任意の fiber 頂点を参照点とする接続同値で全基点の π 同型を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedFiber)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
open SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (KanPiIsomorphism)
variable (A : Type u) [CommRing A]

/-- 同じ指定随伴構造射は零次数を含め、全基点で π 同型。 -/
lemma gammaAdjointSuspension_kanPiIsomorphism (M : Complex A) :
    KanPiIsomorphism ((gammaAdjointSuspension A).app M).right := by
  have := gammaPointedFunctor_preservesFiniteLimits A
  have := gammaPointedFunctor_preservesZeroMorphisms A
  have := gammaLoopFunctor_preservesFiniteLimits A
  have := gammaLoopFunctor_preservesZeroMorphisms A
  let p := (gammaPointedFunctor A).map (mappingCone.triangle (𝟙 M)).mor₃
  let q := (gammaLoopFunctor A).map (mappingCone.triangle (𝟙 M)).mor₃
  let f := (gammaAdjointSuspension A).app (mappingCone (𝟙 M))
  let g := (gammaAdjointSuspension A).app (M⟦(1 : ℤ)⟧)
  have h : p ≫ g = f ≫ q :=
    (gammaAdjointSuspension A).naturality (mappingCone.triangle (𝟙 M)).mor₃
  have : Fibration p.right := gammaConeProjection_fibration A (𝟙 M)
  have : Fibration q.right := gammaLoopMap_fibration A _
    (coneProjection_projectiveFibration A (𝟙 M))
  let φ := KST.Spectra.PointedFiberComparison.map p q f g h
  let b := p.right.app _ ((gammaPointedFunctor A).obj (mappingCone (𝟙 M))).basepoint
  let b' := q.right.app _ ((gammaLoopFunctor A).obj (mappingCone (𝟙 M))).basepoint
  have hb : g.right.app _ b = b' :=
    (FibrationSquare.base_eq p.right q.right f.right g.right
      (congrArg Under.Hom.right h) _).trans
        (congrArg (q.right.app _) (pointedMap_basepoint f))
  have hg (n : ℕ) : Function.Bijective (KanHomotopyGroup.map (n := n) g.right hb) :=
    KanHomotopy.map_bijective_congr (n + 1) g.right
      (pointedMap_basepoint p).symm (pointedMap_basepoint q).symm
      (pointedMap_basepoint g) hb
      (gammaAdjointSuspension_bijective_at_basepoint A (M⟦(1 : ℤ)⟧) (n + 1))
  have hφ : KanPiIsomorphism φ.right :=
    contractibleFiberMapOver_piIsomorphism p.right q.right f.right g.right
      (congrArg Under.Hom.right h)
      (fun e n => gammaIdentityCone_homotopy_subsingleton A M n e)
      (fun e n => gammaLoopIdentityCone_homotopy_subsingleton A M n e)
      (gammaIdentityCone_terminal_rlp A M) (gammaLoopIdentityCone_terminal_rlp A M)
      b b' hb hg φ.right (congrArg Under.Hom.right
        (KST.Spectra.PointedFiberComparison.map_ι p q f g h))
  let eF := pointedConeFiberIso A (gammaPointedFunctor A) (𝟙 M)
  let eG := pointedConeFiberIso A (gammaLoopFunctor A) (𝟙 M)
  let iF : ((gammaPointedFunctor A).obj M).right ≅ (pointedFiber p).right :=
    PointedSimplicialSet.forget.mapIso eF
  let iG : ((gammaLoopFunctor A).obj M).right ≅ (pointedFiber q).right :=
    PointedSimplicialSet.forget.mapIso eG
  have hn : iF.hom ≫ φ.right = ((gammaAdjointSuspension A).app M).right ≫ iG.hom :=
    congrArg Under.Hom.right (pointedConeFiberIso_naturality A
      (gammaPointedFunctor A) (gammaLoopFunctor A) (gammaAdjointSuspension A) (𝟙 M))
  have hc := (KanPiIsomorphism.of_iso iF).comp hφ
  rw [hn] at hc
  exact hc.of_comp (KanPiIsomorphism.of_iso iG)

end SerrePositivity.EInfinity.PowerOperation
