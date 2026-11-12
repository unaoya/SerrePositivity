module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：指定部分 path と全パラメータの二端点を合わせた有限な相対 path 境界。
方針：区間境界と部分複体の積の和を使う。
規約：path は第一因子、比較ホモトピーの時間は後で右に加える。
使われ方：指定部分 path を保つ有限模型の単射境界近似。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K : SSet.{u}} (A : K.Subcomplex)

/-- 概要：部分 path と両端を合わせた相対境界の形状。
方針：二部分複体の積の和。規約：第一因子が path。使われ方：有限相対近似の境界。 -/
def relativePathBoundaryShape : SSet.{u} := Subcomplex.unionProd (boundary 1) A

/-- 概要：相対境界の全 path 形状への包含。
方針：部分複体の包含。規約：単射。使われ方：境界固定の有限模型の入力。 -/
def relativePathBoundaryι : relativePathBoundaryShape A ⟶ (Δ[1] : SSet.{u}) ⊗ K :=
  (Subcomplex.unionProd (boundary 1) A).ι

/-- 概要：相対 path 境界の包含は単射。
方針：部分複体の包含。規約：有限性は不要。使われ方：相対近似と相対輸送。 -/
instance relativePathBoundaryι_mono : Mono (relativePathBoundaryι A) :=
  inferInstanceAs (Mono (Subcomplex.unionProd (boundary 1) A).ι)

/-- 概要：有限形状の相対 path 境界は有限。
方針：有限な区間直積の部分複体。規約：部分複体に別の有限性仮定は不要。
使われ方：全境界を持つ有限因子分解。 -/
instance relativePathBoundaryShape_finite [K.Finite] : (relativePathBoundaryShape A).Finite :=
  inferInstanceAs (SSet.Finite (Subcomplex.unionProd (boundary 1) A))

/-- 概要：指定部分 path から相対境界への射。
方針：積の和の第一包含。規約：部分 path 全体。使われ方：指定 path 制限の保持。 -/
def relativePathBoundarySide : (Δ[1] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶
    relativePathBoundaryShape A := Subcomplex.unionProd.ι₁ (boundary 1) A

/-- 概要：全パラメータの両端から相対境界への射。
方針：積の和の第二包含。規約：両端を同時に扱う。使われ方：二入力の保持。 -/
def relativePathBoundaryEnds : (boundary 1 : SSet.{u}) ⊗ K ⟶ relativePathBoundaryShape A :=
  Subcomplex.unionProd.ι₂ (boundary 1) A

/-- 概要：部分 path は元の部分複体の包含で全 path に入る。
方針：積の和の包含式。規約：厳密な式。使われ方：比較円柱の部分制限。 -/
lemma relativePathBoundarySide_ι :
    relativePathBoundarySide A ≫ relativePathBoundaryι A = (Δ[1] : SSet.{u}) ◁ A.ι :=
  Subcomplex.unionProd.ι₁_ι _ _

/-- 概要：両端は区間境界の包含で全 path に入る。
方針：積の和の包含式。規約：厳密な式。使われ方：比較円柱の端点制限。 -/
lemma relativePathBoundaryEnds_ι :
    relativePathBoundaryEnds A ≫ relativePathBoundaryι A = (boundary 1).ι ▷ K :=
  Subcomplex.unionProd.ι₂_ι _ _

/-- 概要：相対境界の指定端点。
方針：境界内の指定端点を第二包含へ合成する。
規約：零が始点。使われ方：二入力と模型の端点を照合する。 -/
def relativePathBoundaryEndpoint (e : Fin 2) : K ⟶ relativePathBoundaryShape A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint e K ≫ relativePathBoundaryEnds A

/-- 概要：相対境界の指定端点は元の prism の指定端点。
方針：両包含の式を合成する。規約：両端。使われ方：端点の厳密な追跡。 -/
lemma relativePathBoundaryEndpoint_ι (e : Fin 2) :
    relativePathBoundaryEndpoint A e ≫ relativePathBoundaryι A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint e K := by
  rw [relativePathBoundaryEndpoint, Category.assoc, relativePathBoundaryEnds_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι]

/-- 概要：指定部分 path の端点と全形状の端点は相対境界内で一致する。
方針：単射な全 path への包含後に両端の式を照合する。
規約：元の部分複体の包含。使われ方：境界輸送の二入力への制限。 -/
lemma relativePathBoundarySide_endpoint (e : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint e (A : SSet.{u}) ≫ relativePathBoundarySide A =
      A.ι ≫ relativePathBoundaryEndpoint A e := by
  apply (cancel_mono (relativePathBoundaryι A)).1
  rw [Category.assoc, relativePathBoundarySide_ι, Category.assoc,
    relativePathBoundaryEndpoint_ι]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
