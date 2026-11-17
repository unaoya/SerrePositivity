module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawModules
public import SerrePositivity.EInfinity.Modules.DGResolutionAdjunction
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNerveSource
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.DGModuleResolutionLocalization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion

/-!
# 元の BE 加群の通常 nerve から指定半自由模型への源

概要：HA §1.3.5 の同じ dg 半自由分解へ、元の閉零加群の全 nerve を送る。
方針：Hom の持ち上げを戻して閉零列を dg 単体にし、指定分解を適用する。
規約：通常 nerve からの局所化普遍性は別に証明する。
使われ方：M10 の元の固定底の相対局所化と半自由 fiber の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ閉零加群の列を元の dg nerve へ送る（HA Construction 1.3.1.9）。
方針：元の Hom の持ち上げを戻し、高次成分零の同じ dg 単体を取る。
規約：全次元を保持する。使われ方：指定半自由分解への入口。 -/
def strictRawModuleDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶
      dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X)) where
  app Δ := ↾fun s => closedNerveSimplex
    (s ⋙ ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X))
  naturality _ _ f := by
    ext s
    exact closedNerveSimplex_pullback (A := A)
      (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (s ⋙ ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)) f.unop.toOrderHom

/-- 概要：同じ通常加群の源から指定半自由模型への全関手（HA §1.3.5）。
方針：元の dg nerve の源の後に同じ実分解を適用する。
規約：元の入力の射影性を要求しない。使われ方：M10 の固定底比較の源。 -/
def strictRawModuleSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶ strictModuleInfinity A X :=
  strictRawModuleDGSource A X ≫
    moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))

/-- 概要：dg 源は元の同じ加群を頂点に取る（HA Construction 1.3.1.9）。
方針：同じ閉零列の零次の対象を評価する。
規約：Hom の持ち上げだけを戻す。使われ方：指定分解の頂点の照合。 -/
lemma strictRawModuleDGSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
        ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M)) := by
  apply (Simplex.vertexEquiv (A := A)
    (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).injective
  rfl

/-- 概要：dg 源の同じ一単体は元の閉零射（HA Construction 1.3.1.9）。
方針：dg nerve の辺同値で唯一の閉零成分を照合する。
規約：指定された元の射。使われ方：元の擬同型の反転。 -/
lemma strictRawModuleDGSource_edge (X : (operad A).Algebra)
    {M N : (strictRawModuleRelativeCategory A X).category} (f : M ⟶ N) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (dgClosedEdge A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) f.down).edge := by
  apply (dgNerve.edgeEquiv A _).injective
  change dgNerve.edgeEquiv A _
    ((closedNerveInclusion A _).app _
      ((ComposableArrows.mk₁ f) ⋙ ULiftHom.down.{u,u+1,u+1}
        (C := strictRawModuleCategory A X))) = _
  rw [closedNerveInclusion_edge]
  change _ = Simplex.edgeEquiv ((Simplex.edgeEquiv (A := A)
    (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
      ⟨pairObj
        (ForgetEnrichment.to (Complex A)
          ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M))
        (ForgetEnrichment.to (Complex A)
          ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj N)),
        closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
          _ _ f.down⟩)
  rw [Equiv.apply_symm_apply]
  apply Sigma.ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    rfl

/-- 概要：同じ通常加群の源の値は指定された半自由分解（HA §1.3.5）。
方針：同じ dg 源の頂点の式を全関手の合成へ代入する。
規約：対象を選び直さない。使われ方：源の本質的全射性。 -/
lemma strictRawModuleSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
          ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M))) := by
  change (moduleResolution A _).app _ ((strictRawModuleDGSource A X).app _ _) = _
  rw [strictRawModuleDGSource_vertex]

/-- 概要：同じ通常の源は元の全擬同型を反転する（HA Proposition 1.3.5.13 の成分）。
方針：同じ閉零射の dg 辺と指定半自由分解の反転の法則を使う。
規約：通常 nerve の局所化普遍性は主張しない。使われ方：M10 の固定底の比較。 -/
lemma strictRawModuleSource_inverts (X : (operad A).Algebra) :
    InvertsEdges (strictRawModuleSource A X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (strictRawModuleRelativeCategory A X)) := by
  intro s hs
  obtain ⟨M, N, f, hf, rfl⟩ := hs
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  have h := dgModuleResolvedInfinity_invertsQuasiIso A (RightModule A D) D
    (DGFunctor.id (RightModule A D)) (dgClosedEdge A (RightModule A D) f.down)
    (by rw [dgClosedEdge_closed]; exact hf)
  apply (isInvertibleEdge_congr (X := strictModuleInfinity A X)
    (e := (edgeOfSimplex (ComposableArrows.mk₁ f)).map
      ((truncation 2).map (strictRawModuleSource A X)))
    (f := (dgClosedEdge A (RightModule A D) f.down).map
      ((truncation 2).map (moduleResolution A D))) ?_).mpr h
  change (moduleResolution A D).app (Opposite.op ⦋1⦌)
    ((strictRawModuleDGSource A X).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) = _
  rw [strictRawModuleDGSource_edge]
  rfl

/-- 概要：同じ通常の源は半自由模型の全対象を同値まで覆う（HA §1.3.5）。
方針：元の半自由加群を入力し、同じ分解の包含上の恒等比較を評価する。
規約：全関手の分解を保持する。使われ方：固定底の局所化比較の対象の側。 -/
lemma strictRawModuleSource_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleSource A X) := by
  intro y
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  obtain ⟨P, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := SemifreeDGModules A D)).symm.surjective y
  let M : strictRawModuleCategory A X := ForgetEnrichment.of (Complex A) P.val
  refine ⟨ComposableArrows.mk₀ ((ULiftHom.up.{u,u+1,u+1}
    (C := strictRawModuleCategory A X)).obj M), ⟨?_⟩⟩
  have e := (dgModuleResolutionRetractIso A D).app (Simplex.vertex (A := A) P)
  change VertexIso
    ((moduleResolution A D).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (semifreeInclusion A D)).app (Opposite.op ⦋0⦌) (Simplex.vertex (A := A) P)))
    (Simplex.vertex (A := A) P) at e
  rw [dgFunctorNerve_vertex] at e
  change VertexIso
    ((strictRawModuleSource A X).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ ((ULiftHom.up.{u,u+1,u+1}
        (C := strictRawModuleCategory A X)).obj M))) (Simplex.vertex (A := A) P)
  rw [strictRawModuleSource_vertex]
  exact e

attribute [cite HA "1.3.1.9" (partial := component)
  "同じ閉零加群列を元の dg nerve の全単体へ送る源と指定頂点・辺の照合。"]
  strictRawModuleDGSource strictRawModuleDGSource_vertex strictRawModuleDGSource_edge
attribute [cite HA "1.3.5.13" (partial := component)
  "同じ指定半自由分解への源・擬同型の反転・本質的全射性。通常 nerve からの普遍性は含まない。"]
  strictRawModuleSource strictRawModuleSource_vertex strictRawModuleSource_inverts
  strictRawModuleSource_essentiallySurjective

end SerrePositivity.EInfinity.BarrattEccles
