module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaWeakEquivalence
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTruncation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncationInclusionNaturality

/-!
# Γ の各段は準同型を全基点 π 同型へ送る

DAG XIII §2.2 の導来圏への降下の前段。同じ smart 切断を使い、
零次数の境界も含めて準同型性を運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable {A : Type u} [CommRing A]

/-- 同じ非負鎖複体としての smart 切断は準同型を保つ。 -/
lemma smartTruncationMap_quasiIso {M N : Complex A} (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  have ht : QuasiIso (truncLEMap f e) :=
    (quasiIso_truncLEMap_iff f e).mpr (fun _ _ _ => inferInstance)
  have he : QuasiIso (extendMap (truncLE'Map f e) e) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (M.truncLEIso e).symm (N.truncLEIso e).symm
        (_root_.SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality f e).symm)).mpr ht
  exact (quasiIso_extendMap_iff (truncLE'Map f e) e).mp he

/-- Γ の台は、準同型を零次数・全基点で π 同型へ送る。 -/
lemma gammaMap_kanPiIsomorphism {M N : Complex A} (f : M ⟶ N) [QuasiIso f] :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map f) :=
  (gammaMap_kanPiIsomorphism_iff A f).mpr (smartTruncationMap_quasiIso f)

/-- 元の複体の準同型は、シフトした各段でも同じ π 同型となる。 -/
lemma levelMap_kanPiIsomorphism {M N : Complex A} (f : M ⟶ N) [QuasiIso f] (r : ℕ) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((levelSpaceFunctor A r).map f) := by
  exact gammaMap_kanPiIsomorphism (f⟦(r : ℤ)⟧')

end SerrePositivity.EInfinity.PowerOperation
