module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting
public import SerrePositivity.InfinityCategories.Core.MappingSpaceTrivialFibration
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：同型な終点に沿って元の pinched Hom の同値を構成する。
方針：可逆 path の二つの端点評価の充満忠実性で共通の Hom を比較する。
規約：頂点同型を厳密な頂点等号で置き換えない。
使われ方：end の分類図式の全自然同型を写像空間へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：終点の元の頂点同型は同じ始点からの写像空間の同値を与える。
方針：同型を表す可逆辺と始点の定値 path を取り、二端点の Hom 比較を合成する。
規約：始点は固定し、追加の fibration 仮定を要求しない。
使われ方：分類同型を使った二変数 Hom の正規化。 -/
def pinchedHomTargetVertexIsoEquivalence {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y z : X _⦋0⦌} (i : VertexIso y z) :
    QCatEquivalence (pinchedHom x y) (pinchedHom x z) := by
  let s := (homotopyCategory_homMk_surjective y z i.hom).choose
  have hs := (homotopyCategory_homMk_surjective y z i.hom).choose_spec
  have hi : IsInvertibleEdge s := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk s)
    rw [hs]
    infer_instance
  let a := (equivalencePathRefl X).app (Opposite.op ⦋0⦌) x
  let b := equivalencePathVertex s hi
  have ha (j : Fin 2) : (equivalencePathEndpoint X j).app (Opposite.op ⦋0⦌) a = x := by
    exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (equivalencePathRefl_endpoint X j)
  have hb₀ : (equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) b = y :=
    equivalencePathVertex_zero s hi
  have hb₁ : (equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) b = z :=
    equivalencePathVertex_one s hi
  let e₀ := ((isFullyFaithful_of_trivialKanFibration
    (equivalencePathEndpoint X 0)) a b).isQCatEquivalence.choose
  let e₁ := ((isFullyFaithful_of_trivialKanFibration
    (equivalencePathEndpoint X 1)) a b).isQCatEquivalence.choose
  let t₀ : pinchedHom ((equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) a)
      ((equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) b) ≅ pinchedHom x y :=
    eqToIso (congrArg₂ (fun v w : X _⦋0⦌ ↦ pinchedHom v w) (ha 0) hb₀)
  let t₁ : pinchedHom ((equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) a)
      ((equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) b) ≅ pinchedHom x z :=
    eqToIso (congrArg₂ (fun v w : X _⦋0⦌ ↦ pinchedHom v w) (ha 1) hb₁)
  exact (e₀.trans (qCatEquivalenceOfIso t₀)).symm.trans (e₁.trans (qCatEquivalenceOfIso t₁))

end SerrePositivity.InfinityCategories.F2.Presentable
