module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationIso

/-!
概要：同じ元三因子の全実逆回転を native 全関手同型として保持する。
方針：元全厳密比較の全ホモトピーと同じ K(D) 成分同値を使う。
規約：元指定成分と全 Hom 作用を保持する。
使われ方：元 gluing の cone 族と固定 ν の合成全比較への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : StrictNatTrans F G)
local notation "L" => dgModuleNaturalInverseRotationSource R D F G η
local notation "θ" => dgModuleNaturalInverseRotation R D F G η

/-- 概要：元全実逆回転ホモトピーは全頂点で可逆。
方針：元閉成分の同じ native 辺を回収し三因子の同値を適用。
規約：元全ホモトピー不変。使われ方：native 全比較への束ね。 -/
lemma dgModuleNaturalInverseRotation_pointwise (z : (dgNerve R P) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (θ).homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (L) G (θ) x
  have hc : (θ).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (L) G (θ) x).symm
  have he := dgStrictNatTrans_homotopy_vertex_edge (θ) x
  rw [hc] at he
  apply (isInvertibleEdge_congr he).mpr
  haveI := dgModuleEdge_isIso_of_homotopy R D a
    (dgModuleNaturalInverseRotation_isIso R D F G η x)
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge R D a).toTruncated)

/-- 概要：同じ元実逆回転の native 全関手同型。
方針：元全ホモトピーと三因子の同じ実成分同値を束ねる。
規約：全比較を成分同値の任意選択で代用しない。
使われ方：元 gluing cone・固定 ν の実合成全比較。 -/
def dgModuleNaturalInverseRotationNerveComparison : FunctorIso (dgNerve.map (L)) (dgNerve.map G) :=
  functorIsoOfPointwiseInvertibleHomotopy (θ).homotopy
    (dgModuleNaturalInverseRotation_pointwise R D F G η)
end SerrePositivity.KST.SConstruction
