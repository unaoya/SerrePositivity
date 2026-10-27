module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTransIso

/-!
概要：元全厳密比較の K(D) 同値成分を同じ native 全関手同型へ束ねる。
方針：元閉成分の辺を回収し K(D) の可逆性を native 辺へ反映する。
規約：元全ホモトピーを使用する。
使われ方：元小模型の評価を保つ cone 全図式比較の native 可逆性。
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
  (ha : ∀ x, IsIso ((moduleToHomotopy R D).map
    (dgModuleNaturalConeArrow R D F G η x)))
include ha

/-- 概要：元 K(D) 同値成分を持つ全厳密比較は全頂点で可逆。
方針：同じ全ホモトピーの頂点辺を元閉成分の native 辺へ回収する。
規約：同じ元全ホモトピーを保持。使われ方：cone square 全比較の可逆性。 -/
lemma dgModuleKStrictNatTrans_pointwise (z : (dgNerve R P) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge η.homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D F G η x
  have hc : η.app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D F G η x).symm
  have he := dgStrictNatTrans_homotopy_vertex_edge η x
  rw [hc] at he
  apply (isInvertibleEdge_congr he).mpr
  haveI := dgModuleEdge_isIso_of_homotopy R D a (ha x)
  exact (edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge R D a).toTruncated)

/-- 概要：同じ元全厳密比較の K(D) 同値成分を保持する native 全関手同型。
方針：元全ホモトピーと証明済み全頂点可逆性を束ねる。
規約：元全比較を成分同値の選択で置き換えない。
使われ方：元評価同型を保つ cone square 全比較。 -/
def dgModuleFunctorIsoOfKStrictNatTrans : FunctorIso (dgNerve.map F) (dgNerve.map G) :=
  functorIsoOfPointwiseInvertibleHomotopy η.homotopy
    (dgModuleKStrictNatTrans_pointwise R D F G η ha)
end SerrePositivity.KST.SConstruction
