module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionHomotopyInvertible
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransVertexClosed
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransNerveHom
/-!
概要：点ごとに準同型な同じ厳密 dg 自然変換を、可逆な実全関手射へ送る。
方針：元の閉射の回収と実出力分解による頂点辺の反転を使う。
規約：出力の射影性・始域の Small 性は不要。使われ方：模型変更の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
open DGNerve.HomotopyComparison
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleResolution_strictNatTrans_isIso_of_quasiIso
    (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) (E : Type v)
    [DGCategory R C] [DGCategory R E] [Small.{u} E]
    {F G : DGFunctor R C (RightModule R E)}
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (ha : ∀ x y, F.map x y ≫ moduleHomPostcompose R E _ _ _ (a y) =
      G.map x y ≫ moduleHomPrecompose R E _ _ _ (a x))
    (hq : ∀ x, moduleQuasiIso R E (a x)) :
    IsIso (functorHomPostcomp (dgNerve.map F) (dgNerve.map G)
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (dgStrictNatTransNerveHom R C (RightModule R E)
        (dgModuleStrictNatTransOfHomNaturality R E a ha))) := by
  rw [dgStrictNatTransNerveHom_spec]
  apply dgModuleResolution_homotopy_isIso_of_quasiIso_vertex
  intro z
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  change moduleQuasiIso R E (edgeClosed (simplicialHomotopyVertexEdge
    (dgModuleStrictNatTransOfHomNaturality R E a ha).homotopy (Simplex.vertex x)).toTruncated)
  rw [dgModuleStrictNatTrans_homotopy_vertex_closed]
  exact hq x
end
end SerrePositivity.InfinityCategories
