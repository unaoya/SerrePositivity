module

public import SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery
public import SerrePositivity.KST.LocalizingInvariants.TerminalPullbackFamilyComparison
public import SerrePositivity.KST.LocalizingInvariants.VerdierParametricSourceIso

/-!
概要：元の有限回収の実円柱の前段を、元の全正方形族へ二脚固定で比較する。
方針：保存済みの二つの厳密射影式を同じ実 corner のファイバー比較へ代入する。
規約：比較対象は回収した同じ実全族であり、cospan と終端列は比較の全時刻で恒等。
使われ方：実余錐円柱の商像と元の分数評価正方形の境界整合を構成する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance recoveredComparisonFiniteLimits {X : SSet.{u}} [Quasicategory X]
    [IsStable X] : HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance recoveredComparisonParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 同じ実回収の pullback 円柱を、元の全正方形族へ二脚上で恒等な実辺で比較する。 -/
def VerdierFiniteMappingCoconeRecovery.pullbackComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    TerminalPullbackFamilyComparison n r.cylinder.pullbacks
      (parametricPullbackDiagramFamily r.square r.square_pullback) :=
  Classical.choice (exists_terminalPullbackFamilyComparison n r.cylinder.pullbacks
    (parametricPullbackDiagramFamily r.square r.square_pullback)
    r.cylinder.pullbacks_projection r.cylinder.pullbacks_terminal)

/-- 二脚固定の同じ比較辺を始域頂点で評価した、元の二つの前段全族の比較辺。 -/
def VerdierFiniteMappingCoconeRecovery.pullbackSourceComparisonEdge
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    Truncated.Edge (X := (truncation 2).obj
      ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj)))
      (functorVertex (pullbackSourcePrefixFamily r.cylinder.pullbacks))
      (functorVertex (pullbackSourcePrefixFamily
        (parametricPullbackDiagramFamily r.square r.square_pullback))) :=
  r.pullbackComparison.edge.map ((truncation 2).map
    ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map
      ((ihom (Δ[n] : SSet.{u})).map
        ((fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
          evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
            (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))))

lemma VerdierFiniteMappingCoconeRecovery.pullbackSourceComparisonEdge_isInvertible
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    IsInvertibleEdge r.pullbackSourceComparisonEdge :=
  r.pullbackComparison.isInvertible.map _

/-- 前段比較の順方向の射は、二脚固定の元の比較辺を評価した同じ辺の類。 -/
def VerdierFiniteMappingCoconeRecovery.pullbackSourceComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    FunctorIso (pullbackSourcePrefixFamily r.cylinder.pullbacks)
      (pullbackSourcePrefixFamily
        (parametricPullbackDiagramFamily r.square r.square_pullback)) := by
  have := r.pullbackSourceComparisonEdge_isInvertible
  exact asIso (Truncated.HomotopyCategory.homMk r.pullbackSourceComparisonEdge)

/-- 実余錐円柱の全前段を、元の全正方形族の前段へ同じ比較辺で接続する。 -/
def VerdierFiniteMappingCoconeRecovery.cylinderPrefixComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    FunctorIso
      (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
      (pullbackSourcePrefixFamily
        (parametricPullbackDiagramFamily r.square r.square_pullback)) := by
  rw [r.cylinder.homotopy_prefix]
  exact r.pullbackSourceComparison

/-- 回収済みの同じ実余錐円柱の全前段の商像を、元の定値図式へ比較する。 -/
def VerdierFiniteMappingCoconeRecovery.cylinderPrefixQuotientIso
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    FunctorIso
      (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom)
      (SSet.const (functorVertex (D ≫ q.hom)) : S.toSSet ⊗ (Δ[1] : SSet.{u}) ⟶ _) := by
  let e : FunctorIso
      ((r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom)
      (pullbackSourcePrefixFamily (parametricPullbackDiagramFamily r.square r.square_pullback) ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom) :=
    VertexIso.map r.cylinderPrefixComparison
      ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map ((ihom (Δ[n] : SSet.{u})).map q.hom))
  exact e ≪≫ verdierParametricSourceIso h D r.square r.square_pullback
    r.square_original r.square_denominators

lemma VerdierFiniteMappingCoconeRecovery.cylinderPrefixQuotient_invertsAllEdges
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    InvertsEdges
      (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom) Set.univ :=
  (invertsEdges_functorIso_iff r.cylinderPrefixQuotientIso Set.univ).mpr
    (invertsEdges_const _ _ _ Set.univ)

end SerrePositivity.KST.LocalizingInvariants
