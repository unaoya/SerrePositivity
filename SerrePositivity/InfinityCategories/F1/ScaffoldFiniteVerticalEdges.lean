module

public import SerrePositivity.InfinityCategories.F1.ScaffoldFiniteCocartesianEdge
public import SerrePositivity.InfinityCategories.F1.ScaffoldFiniteFiberComparison

/-!
概要：有限鎖上の scaffold の最初の係数の prism とその垂直辺。
方針：円柱比較の底への射を計算し、最初の辺の cocartesian 性を全空間へ持ち上げる。
規約：元の全空間の射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の垂直辺の条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：scaffold の最初の係数の prism から全空間への比較。
方針：写像円柱の左包含と全 replacement への比較に scaffold の射を後合成する。
規約：始域の係数は零頂点の値。
使われ方：Kerodon Theorem 5.3.5.7、区間上の比較の円柱部分。 -/
noncomputable def scaffoldFiniteScaffoldPrism (n : ℕ) {E : SSet.{u}}
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ E :=
  pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
    scaffoldFiniteCylinderComparison n F ≫ l

/-- 概要：最初の係数の prism は有限鎖の最初の辺を被覆する。
方針：区間部分の比較の式と初期係数の組み立て射の射影を計算する。
規約：h は scaffold の底上の可換性。
使われ方：Kerodon Theorem 5.3.5.7、垂直辺の底への像。 -/
lemma scaffoldFiniteScaffoldPrism_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ p =
      fst Δ[1] (F.obj (ULift.up 0)) ≫
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n) := by
  rw [scaffoldFiniteScaffoldPrism, Category.assoc, Category.assoc, h,
    ← Category.assoc, scaffoldFiniteCylinderComparison_inl, Category.assoc,
    simplicialReplacementInitialAssembly_projection, whiskerRight_fst]

/-- 概要：最初の係数の prism は合成した区間への射影を被覆する。
方針：有限鎖の最初の辺が区間への射の切断であることを使う。
規約：標的の区間の射影は直積の第一射影。
使われ方：Kerodon Theorem 5.3.5.7、区間上の比較の底の条件。 -/
lemma scaffoldFiniteScaffoldPrism_interval_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ (p ≫ scaffoldFiniteCollapse n) =
      fst Δ[1] (F.obj (ULift.up 0)) := by
  rw [← Category.assoc, scaffoldFiniteScaffoldPrism_projection n p F l h]
  simp only [Category.assoc, scaffoldFiniteCollapse_firstEdge, Category.comp_id]

/-- 概要：prism の指定係数頂点を固定した垂直一単体。
方針：標準区間の恒等一単体と係数頂点の定値一単体を組にして評価する。
規約：辺の向きは時刻零から一。
使われ方：Kerodon Theorem 5.2.4.1、各係数頂点に対する cocartesian 条件。 -/
def prismVerticalSimplex {K E : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (x : K _⦋0⦌) : E _⦋1⦌ :=
  H.app (Opposite.op ⦋1⦌)
    (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), PinchedHom.constant x 1)

/-- 概要：scaffold の最初の係数の prism の各垂直辺は区間への射に関して cocartesian。
方針：垂直辺の底への像を最初の辺と同定し、left fibration と合成の定理を使う。
規約：係数値の Kan 性や fiber 比較の同値性はこの条件には不要。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の第三条件。 -/
lemma scaffoldFiniteScaffoldPrism_vertical_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    IsCocartesianEdge (p ≫ scaffoldFiniteCollapse n)
      (prismVerticalSimplex (scaffoldFiniteScaffoldPrism n F l) x) := by
  apply scaffoldFiniteInitialEdge_comp_isCocartesian n p
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), PinchedHom.constant x 1))
    (scaffoldFiniteScaffoldPrism_projection n p F l h)
  change p.app (Opposite.op ⦋1⦌)
    (prismVerticalSimplex (scaffoldFiniteScaffoldPrism n F l) x) =
      SSet.yonedaEquiv ((stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) at he
  rw [scaffoldFiniteInitialEdge_yoneda] at he
  exact he

end SerrePositivity.InfinityCategories
