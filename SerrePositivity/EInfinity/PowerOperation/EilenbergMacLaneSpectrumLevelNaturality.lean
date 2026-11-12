module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumCohomology
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStageCohomologyNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
# 実 EM スペクトルの同じ置換射を通る段ごとの π/H 自然性

DAG XIII §2.2 の整数 π/H の全関手比較への前段。元の列の射と同じ逐次置換射の
厳密な可換式を、標準基点の群の可換式へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (KanSequence pointedGroupMap)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
variable (A : Type u) [CommRing A]

/-- 実スペクトルの同じ段の射は、元の列への指定置換射と厳密に可換する。 -/
lemma eilenbergMacLaneSpectrumMap_projection {M N : Complex A} (f : M ⟶ N) (r : ℕ) :
    ((eilenbergMacLaneSpectrumFunctor A).map f).app r ≫
      (KanSequence.replacementProjection (eilenbergMacLaneSequence A N)).app r =
    (KanSequence.replacementProjection (eilenbergMacLaneSequence A M)).app r ≫
      (levelPointedFunctor A r).map f :=
  congrArg (fun k : (eilenbergMacLaneSequence A M).cofibrantReplacement ⟶
    eilenbergMacLaneSequence A N => k.app r)
    (kanSequenceReplacementMap_projection ((eilenbergMacLaneSequenceFunctor A).map f))

/-- 任意の正次数の計算段で、同じ置換射による実スペクトルの π/H 比較。 -/
def eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt (M : Complex A)
    (j : ℤ) (r n : ℕ) (hj : (n : ℤ) + 1 = j + (r : ℤ)) :
    KanHomotopyGroup (((eilenbergMacLaneSpectrumFunctor A).obj M).level r).space.right n
      (((eilenbergMacLaneSpectrumFunctor A).obj M).level r).space.basepoint ≃*
        Multiplicative (M.homology (-j)) :=
  (KanHomotopyGroup.equivOfPiIsomorphism n
    ((KanSequence.replacementProjection (eilenbergMacLaneSequence A M)).app r).right
    (KanSequence.replacementProjection_piIsomorphism (eilenbergMacLaneSequence A M) r)
    (pointedMap_basepoint _)).trans (levelPiCohomologyEquivAt A M j r n hj)

lemma eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt_naturality
    {M N : Complex A} (f : M ⟶ N) (j : ℤ) (r n : ℕ)
    (hj : (n : ℤ) + 1 = j + (r : ℤ))
    (a : KanHomotopyGroup (((eilenbergMacLaneSpectrumFunctor A).obj M).level r).space.right n
      (((eilenbergMacLaneSpectrumFunctor A).obj M).level r).space.basepoint) :
    eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt A N j r n hj
      (pointedGroupMap n (((eilenbergMacLaneSpectrumFunctor A).map f).app r) a) =
      Multiplicative.ofAdd ((HomologicalComplex.homologyMap f (-j)).hom
        (Multiplicative.toAdd
          (eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt A M j r n hj a))) := by
  let p := (KanSequence.replacementProjection (eilenbergMacLaneSequence A M)).app r
  let q := (KanSequence.replacementProjection (eilenbergMacLaneSequence A N)).app r
  let sf := ((eilenbergMacLaneSpectrumFunctor A).map f).app r
  let lf := (levelPointedFunctor A r).map f
  have hs := KanHomotopyGroup.map_square p.right q.right sf.right lf.right
    (congrArg Under.Hom.right (eilenbergMacLaneSpectrumMap_projection A f r)).symm
    (pointedMap_basepoint p) (pointedMap_basepoint q)
    (pointedMap_basepoint sf) (pointedMap_basepoint lf) n a
  have h₁ := congrArg (levelPiCohomologyEquivAt A N j r n hj) hs.symm
  have h₂ := levelPiCohomologyEquivAt_naturality f j r n hj (pointedGroupMap n p a)
  have hp := KanHomotopyGroup.equivOfPiIsomorphism_apply n p.right
    (KanSequence.replacementProjection_piIsomorphism (eilenbergMacLaneSequence A M) r)
    (pointedMap_basepoint p) a
  have hq := KanHomotopyGroup.equivOfPiIsomorphism_apply n q.right
    (KanSequence.replacementProjection_piIsomorphism (eilenbergMacLaneSequence A N) r)
    (pointedMap_basepoint q) (pointedGroupMap n sf a)
  exact (congrArg (levelPiCohomologyEquivAt A N j r n hj) hq).trans
    ((h₁.trans h₂).trans (congrArg (fun t => Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap f (-j)).hom
        (Multiplicative.toAdd (levelPiCohomologyEquivAt A M j r n hj t)))) hp.symm))

end SerrePositivity.EInfinity.PowerOperation
