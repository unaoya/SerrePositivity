module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeSourceTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# 元の通常加群図式と自然変換の同じ導来源による像

概要：M10 の全評価図式と同じ自然変換円柱を指定半自由模型へ送る。
方針：元の ULiftHom 表示・nerve の自然変換円柱・既存の弱辺反転を使う。
規約：HA §1.3.4、同じ全円柱の成分を保持する。
使われ方：全 frame 単体の augmentation と評価による実屋根。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open NerveComparison FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions IsomorphismsAndIsofibrations
open FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  {I : Type (u + 1)} [Category.{u + 1} I]

/-- 概要：元の通常加群図式の同じ導来源による全像。
方針：同じ ULiftHom 関手で元の相対圏へ入れて同じ源を後合成する。
規約：HA §1.3.4、全通常鎖。使われ方：全評価図式の指定模型への像。 -/
def strictRawModuleDiagramSource (F : I ⥤ strictRawModuleCategory A X) :
    nerve I ⟶ strictModuleInfinity A X :=
  nerveMap (F ⋙ ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) ≫
    strictRawModuleSource A X

private lemma mappedNerveEdge_invertible {C : Type (u + 1)} [Category.{u + 1} C]
    {Y : SSet.{u + 1}} (F : nerve C ⟶ Y) {c d : C} (f : c ⟶ d)
    (h : IsInvertibleEdge (X := Y)
      ((edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F))) :
    IsInvertibleEdge (((nerve.edgeMk f).map F).toTruncated) :=
  (isInvertibleEdge_congr (X := Y)
    (e := (edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F))
    (f := ((nerve.edgeMk f).map F).toTruncated) rfl).mp h

/-- 概要：元の擬同型成分の同じ通常辺は同じ源で可逆になる。
方針：既存の同じ弱辺集合とその反転を使う。
規約：HA §1.3.4、同じ辺。使われ方：元の全円柱の可逆性。 -/
lemma strictRawModuleSource_edge_weak {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f) :
    IsInvertibleEdge
      (((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
        (C := strictRawModuleCategory A X)).map f)).map (strictRawModuleSource A X)).toTruncated) := by
  exact mappedNerveEdge_invertible (strictRawModuleSource A X)
    ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).map f)
    (strictRawModuleSource_inverts A X ⟨_, _, _, hf, rfl⟩)

variable {F G : I ⥤ strictRawModuleCategory A X}

/-- 概要：元の自然変換の同じ全通常円柱を同じ導来源へ送る。
方針：既存の nerve 円柱を同じ源で後合成する。
規約：HA §1.3.4、全単体。使われ方：実評価の全二胞体。 -/
def strictRawModuleDiagramNatTransHomotopy (η : F ⟶ G) :
    SSet.Homotopy (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G) :=
  HomotopyClasses.postHomotopy (strictRawModuleSource A X)
    (nerveNatTransHomotopy (Functor.whiskerRight η
      (ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))))

/-- 概要：同じ全円柱の頂点辺は元の同じ成分射の像。
方針：既存の nerve 円柱の成分式を同じ源で送る。
規約：HA §1.3.4、元の端点。使われ方：評価屋根の成分の照合。 -/
lemma strictRawModuleDiagramNatTransHomotopy_component (η : F ⟶ G) (i : I) :
    (simplicialHomotopyVertexEdge (strictRawModuleDiagramNatTransHomotopy A X η)
      (nerveVertex i)).edge =
    ((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
      (C := strictRawModuleCategory A X)).map (η.app i))).map (strictRawModuleSource A X)).edge :=
  congrArg ((strictRawModuleSource A X).app (op ⦋1⦌))
    (nerveNatTransHomotopy_component (Functor.whiskerRight η
      (ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))) i)

/-- 概要：同じ全自然変換円柱の辺を全関手圏の射として保持する。
方針：同じ円柱の辺のホモトピー類を取る。
規約：HA §1.3.4、成分だけにしない。使われ方：元の全評価二胞体。 -/
def strictRawModuleDiagramNatTransHom (η : F ⟶ G) :
    FunctorHom (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G) :=
  Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (strictRawModuleDiagramNatTransHomotopy A X η))

/-- 概要：元の全成分が擬同型なら同じ全円柱は関手同型になる。
方針：同じ成分辺の反転を同じ全円柱へ適用する。
規約：HA §1.3.4、同じ可逆二胞体。使われ方：全 augmentation の反転。 -/
def strictRawModuleDiagramNatTransIso (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    FunctorIso (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G) := by
  apply functorIsoOfPointwiseInvertibleHomotopy (strictRawModuleDiagramNatTransHomotopy A X η)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  exact (isInvertibleEdge_congr
    (e := (simplicialHomotopyVertexEdge (strictRawModuleDiagramNatTransHomotopy A X η)
      (nerveVertex i)).toTruncated)
    (f := ((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
      (C := strictRawModuleCategory A X)).map (η.app i))).map (strictRawModuleSource A X)).toTruncated)
    (strictRawModuleDiagramNatTransHomotopy_component A X η i)).mpr
      (strictRawModuleSource_edge_weak A X (η.app i) (hη i))

/-- 概要：同じ全円柱の同型の順射は元の同じ円柱の射。
方針：同じ辺の類による asIso の定義を読む。
規約：HA §1.3.4、同じ射。使われ方：全評価屋根の三角式。 -/
lemma strictRawModuleDiagramNatTransIso_hom (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    (strictRawModuleDiagramNatTransIso A X η hη).hom =
      strictRawModuleDiagramNatTransHom A X η := rfl

/-- 概要：元の定値加群図式の同じ導来源による像は同じ頂点の定値図式。
方針：通常の定値 nerve の等式と同じ後合成を使う。
規約：HA §1.3.4、指定頂点。使われ方：実屋根の同じ定値端点。 -/
lemma strictRawModuleDiagramSource_const (M : strictRawModuleCategory A X) :
    strictRawModuleDiagramSource A X ((Functor.const I).obj M) =
      SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M))) := by
  change nerveMap ((Functor.const I).obj ((ULiftHom.up.{u, u + 1, u + 1}
    (C := strictRawModuleCategory A X)).obj M)) ≫ strictRawModuleSource A X = _
  rw [SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const,
    SSet.const_comp]
  rfl

/-- 概要：同じ定値図式の照合を全関手同型として保持する。
方針：同じ全関手等式の同型を取る。
規約：HA §1.3.4、同じ成分。使われ方：全評価屋根の端点移送。 -/
def strictRawModuleDiagramSourceConstantIso (M : strictRawModuleCategory A X) :
    FunctorIso (strictRawModuleDiagramSource A X ((Functor.const I).obj M))
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M)))) :=
  eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (strictRawModuleDiagramSource_const A X M))

end SerrePositivity.EInfinity.BarrattEccles
