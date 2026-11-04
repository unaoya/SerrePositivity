module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRelativeInitialComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension

/-!
概要：保存済み実境界円柱を、元の第一行単体亜群化の K 全円柱へ延長する。
方針：始端を同じ回収済み K 実族に固定し、元の亜群化の Kan 条件を実適用する。
規約：同じ単位・実円柱・始端を保持し、境界をホモトピー類へ落とさない。
使われ方：商 core の全円柱との境界付き比較を構成する実始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => join (Δ[n] : SSet) Δ[0]

namespace VerdierRecoveredInitialComparison
variable (c : VerdierRecoveredInitialComparison r U)

/-- 同じ保存済み K 実全族を元の第一行単体へ移す。 -/
def simplexFamily : K ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (r.cylinder.whole ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) (by
      rw [Category.assoc, ← (pre (joinStdSimplexIso n 0).inv).naturality q.hom,
        ← Category.assoc]
      exact c.initialSource_inverts.comp
        ((pre (joinStdSimplexIso n 0).inv).app C.obj))

lemma simplexFamily_boundary : S.ι ≫ c.simplexFamily =
    (SSet.ι₀ : S.toSSet ⟶ P) ≫ r.simplexCylinder := by
  apply (cancel_mono (relativeFirstRowSimplex q (n + 1)).ι).mp
  change S.ι ≫ (r.cylinder.whole ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) =
    (SSet.ι₀ : S.toSSet ⟶ P) ≫
      (r.cylinder.homotopy.h ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj)
  exact (congrArg (fun k => k ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj)
    r.cylinder.homotopy.h₀).symm.trans (Category.assoc _ _ _)

/-- 元の単位へ送った実 S 円柱。始端は同じ K 実全族の制限。 -/
def completedBoundaryHomotopy : SSet.Homotopy
    (S.ι ≫ (c.simplexFamily ≫ groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})))
    ((SSet.ι₁ : S.toSSet ⟶ P) ≫ r.simplexCylinder ≫ groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})) where
  h := r.simplexCylinder ≫ groupoidCompletionMap _
  h₀ := by
    change (SSet.ι₀ : S.toSSet ⟶ P) ≫ r.simplexCylinder ≫ _ = S.ι ≫ c.simplexFamily ≫ _
    rw [← Category.assoc, ← c.simplexFamily_boundary, Category.assoc]
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end VerdierRecoveredInitialComparison

/-- 元の亜群化上の K 全円柱。元の実 S 円柱を全時刻で厳密に保持する。 -/
structure VerdierRecoveredCompletedCylinder (c : VerdierRecoveredInitialComparison r U) where
  endpoint : K ⟶ groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u})
  homotopy : SSet.Homotopy
    (c.simplexFamily ≫ groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u}))
    endpoint
  boundary_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    r.simplexCylinder ≫ groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u})
  endpoint_boundary : S.ι ≫ endpoint =
    (SSet.ι₁ : S.toSSet ⟶ P) ≫ r.simplexCylinder ≫ groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})

/-- 実円柱の始端と境界を保った延長。有限性や新しい比較仮定は不要。 -/
lemma exists_verdierRecoveredCompletedCylinder (c : VerdierRecoveredInitialComparison r U) :
    Nonempty (VerdierRecoveredCompletedCylinder c) := by
  have hKan : SSet.modelCategoryQuillen.J.rlp
      (CategoryTheory.Limits.terminal.from
        (groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u}))) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨g, hg, H, hH⟩ :=
    SerrePositivity.SimplicialModel.KanMonoEndpointExtension.exists_from_zero S.ι hKan
      (c.simplexFamily ≫ groupoidCompletionMap _) _ c.completedBoundaryHomotopy
  exact ⟨⟨g, H, hH, hg⟩⟩

end SerrePositivity.KST.LocalizingInvariants
