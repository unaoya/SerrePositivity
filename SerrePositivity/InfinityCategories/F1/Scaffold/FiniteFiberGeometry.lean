module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ScaffoldFiberMaps
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteCylinderEndpoints

/-!
概要：有限鎖の scaffold から区間の両端 fiber への射。
方針：充填性に依存しない二つの射とその包含後の式を共用する。
規約：元の宣言名・型・証明本文を保持する。
使われ方：F1 と F1B の共通の幾何的な計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最初の係数値から区間の零 fiber への比較射。
方針：元の零頂点の fiber 比較に全空間の零 fiber 同型を後合成する。
規約：底を保つ条件 h の証明の選択には依存しない。
使われ方：Kerodon Theorem 5.3.5.7、区間上の比較の零端条件。 -/
noncomputable def scaffoldFiniteZeroFiberComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    F.obj (ULift.up 0) ⟶
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
  leftScaffoldFiberMap p F l h (ULift.up 0) ≫ (scaffoldFiniteTotalZeroFiberIso n p).hom

/-- 概要：零端の fiber 比較を全空間へ含めると円柱比較の始点の射になる。
方針：零 fiber 同型の包含後の計算と円柱比較の始点の式を使う。
規約：円柱比較に l を後合成した射の始点で比較する。
使われ方：Kerodon Theorem 5.3.5.7、零端の比較の同定。 -/
lemma scaffoldFiniteZeroFiberComparison_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteZeroFiberComparison n p F l h ≫
        vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      prismEndpoint 0 (F.obj (ULift.up 0)) ≫
        pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
          scaffoldFiniteCylinderComparison n F ≫ l := by
  rw [scaffoldFiniteZeroFiberComparison, Category.assoc, scaffoldFiniteTotalZeroFiberIso_hom_ι]
  change simplicialReplacementConstantLift F (ULift.up 0) ≫ l = _
  rw [← Category.assoc _ _ l, ← Category.assoc _ _ l,
    scaffoldFiniteCylinderComparison_endpoint_zero]

/-- 概要：尾部の replacement から区間の一 fiber への比較射。
方針：scaffold の尾部への底変換に全空間の一 fiber 同型を後合成する。
規約：尾部の図式は scaffoldFiniteTail n ⋙ F。
使われ方：Kerodon Theorem 5.3.5.7、区間上の比較の終端条件。 -/
noncomputable def scaffoldFiniteOneFiberComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    simplicialReplacement (scaffoldFiniteTail n ⋙ F) ⟶
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  leftScaffoldBaseChange p F l h (scaffoldFiniteTail n) ≫ (scaffoldFiniteTotalOneFiberIso n p).hom

/-- 概要：終端の fiber 比較を全空間へ含めると円柱比較の尾部の射になる。
方針：一 fiber 同型の計算と底変換の第一射影の計算を使う。
規約：円柱の尾部に l を後合成する。
使われ方：Kerodon Theorem 5.3.5.7、終端の比較の同定。 -/
lemma scaffoldFiniteOneFiberComparison_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteOneFiberComparison n p F l h ≫
        vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      pushout.inr (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
        scaffoldFiniteCylinderComparison n F ≫ l := by
  rw [scaffoldFiniteOneFiberComparison, Category.assoc, scaffoldFiniteTotalOneFiberIso_hom_ι,
    leftScaffoldBaseChange, pullback.lift_fst, ← Category.assoc,
    scaffoldFiniteCylinderComparison_inr]

end SerrePositivity.InfinityCategories
