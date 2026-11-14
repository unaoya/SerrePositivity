module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneOmegaAllBasepoints
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSequence
public import SerrePositivity.EInfinity.PowerOperation.OmegaSequenceNative
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
# 元の Eilenberg–Mac Lane の Kan 列は全基点の Ω 列である

DAG XIII §2.2 のスペクトル忘却への前段。指定された基本円の構造射と
シフト加法の同型を変えず、全複体・全鎖写像で同じ Ω 列を構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (KanPiIsomorphism)
variable (A : Type u) [CommRing A]

/-- 各段の指定構造射の随伴は、全基点・零次数を含む π 同型。 -/
lemma eilenbergMacLaneSequence_omega (M : Complex A) :
    (eilenbergMacLaneSequence A M).OmegaCondition := by
  intro r
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  let a := ((shiftFunctorAdd' (Complex A) (r : ℤ) 1 ((r + 1 : ℕ) : ℤ)
    (by omega)).inv.app M)
  have : SSet.KanComplex
      ((PointedSimplicialSet.internalHomFunctor PointedSimplicialSet.circle.{u}).obj
        ((gammaPointedFunctor A).obj (M⟦((r + 1 : ℕ) : ℤ)⟧))).right :=
    PointedMapping.basedHom_kanComplex _ _
  have h : KanPiIsomorphism
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        ((gammaPointedFunctor A).map a)).right :=
    KST.Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
      ((gammaPointedFunctor A).map a) (gammaMap_kanPiIsomorphism a)
  change KanPiIsomorphism
    ((adj.homEquiv _ _) (gammaSuspension A (M⟦(r : ℤ)⟧) ≫
      (gammaPointedFunctor A).map a)).right
  rw [Adjunction.homEquiv_naturality_right]
  exact (gammaAdjointSuspension_kanPiIsomorphism A (M⟦(r : ℤ)⟧)).comp h

/-- 元の Kan 列を、証明済みの Ω 条件を持つ同じ充満部分圏の対象として読む。 -/
def eilenbergMacLaneOmegaSequence (M : Complex A) : KanOmegaSequence.{u} :=
  ⟨eilenbergMacLaneSequence A M, eilenbergMacLaneSequence_omega A M⟩

end SerrePositivity.EInfinity.PowerOperation
