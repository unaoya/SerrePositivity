module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCollapse

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCylinder

/-!
概要：有限鎖の scaffold の prism とその底への射影。
方針：fibration の充填性を使わない円柱の式を共用する。
規約：元の宣言名・型・証明本文を保持する。
使われ方：F1 と F1B の共通の幾何的な計算。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：scaffold の最初の係数の prism から全空間への比較。
方針：写像円柱の左包含と全 replacement への比較に scaffold の射を後合成する。
規約：始域の係数は零頂点の値。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の比較の円柱部分。 -/
noncomputable def scaffoldFiniteScaffoldPrism (n : ℕ) {E : SSet.{u}}
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ E :=
  pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (F.obj (ULift.up 0))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderAttachingMap n F) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderComparison n F ≫ l

/-- 概要：最初の係数の prism は有限鎖の最初の辺を被覆する。
方針：区間部分の比較の式と初期係数の組み立て射の射影を計算する。
規約：h は scaffold の底上の可換性。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、垂直辺の底への像。 -/
lemma scaffoldFiniteScaffoldPrism_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ p =
      fst Δ[1] (F.obj (ULift.up 0)) ≫
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n) := by
  rw [scaffoldFiniteScaffoldPrism, Category.assoc, Category.assoc, h,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCylinderComparison_inl, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly_projection, whiskerRight_fst]

/-- 概要：最初の係数の prism は合成した区間への射影を被覆する。
方針：有限鎖の最初の辺が区間への射の切断であることを使う。
規約：標的の区間の射影は直積の第一射影。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の比較の底の条件。 -/
lemma scaffoldFiniteScaffoldPrism_interval_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) =
      fst Δ[1] (F.obj (ULift.up 0)) := by
  rw [← Category.assoc, scaffoldFiniteScaffoldPrism_projection n p F l h]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse_firstEdge, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
