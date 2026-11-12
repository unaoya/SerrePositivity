module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLift

/-!
概要：終点指定の可逆辺の持ち上げ条件と同型による移送。
方針：持ち上げ問題を同型の逆で戻し、得た辺を同型で送る。
規約：可逆辺の像と終点を厳密に固定する。
使われ方：通常の関手空間の持ち上げを全空間の fiber へ渡す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標的の可逆辺を終点指定で持ち上げられる条件。
方針：標準区間からの射を用い、像と終点の厳密な一致を要求する。
規約：この条件だけには inner fibration 性を含めない。
使われ方：底方向の cartesian 輸送の像の比較。 -/
def InvertibleTargetLifting {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ (x : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ B),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)) →
    stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) →
    ∃ l : (Δ[1] : SSet.{u}) ⟶ E,
      stdSimplex.δ (0 : Fin 2) ≫ l = SSet.yonedaEquiv.symm x ∧ l ≫ p = e ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv l))

/-- 概要：相対可逆 path の充填性は終点指定の可逆辺の持ち上げを与える。
方針：path の頂点の持ち上げから区間の辺を取り出す定理を使う。
規約：相対 path の指定端点は一。
使われ方：関手の制限の持ち上げ条件を移送可能な形へまとめる。 -/
lemma invertibleTargetLifting_of_relativePath {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1)] : InvertibleTargetLifting p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanInvertibleEdge_lift_target p

/-- 概要：終点指定の可逆辺の持ち上げは始域と標的の同型で移送できる。
方針：逆同型で持ち上げ問題を戻し、元の射で持ち上げた辺を始域の同型で送る。
規約：可換性は単体集合の射の厳密な等式。
使われ方：内部 Hom の交換と fiber の比較同型に沿う持ち上げ条件の移送。 -/
lemma InvertibleTargetLifting.map_iso {E B E' B' : SSet.{u}}
    {p : E ⟶ B} {p' : E' ⟶ B'} (hp : InvertibleTargetLifting p)
    (a : E ≅ E') (b : B ≅ B') (h : a.hom ≫ p' = p ≫ b.hom) :
    InvertibleTargetLifting p' := by
  intro x e he ht
  have hn : a.inv ≫ p = p' ≫ b.inv := by
    rw [Iso.inv_comp_eq]
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let y := a.inv.app (Opposite.op ⦋0⦌) x
  have hback : stdSimplex.δ (0 : Fin 2) ≫ (e ≫ b.inv) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) y) := by
    rw [← Category.assoc, ht, SSet.yonedaEquiv_symm_comp]
    congr 1
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app hn (Opposite.op ⦋0⦌)) x).symm
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (e ≫ b.inv))) := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)).map ((truncation 2).map b.inv)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (e ≫ b.inv))).edge from SSet.yonedaEquiv_comp e b.inv)).1
      (he.map b.inv)
  obtain ⟨l, hlt, hlp, hli⟩ := hp y (e ≫ b.inv) hi hback
  refine ⟨l ≫ a.hom, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hlt, SSet.yonedaEquiv_symm_comp]
    congr 1
    exact ConcreteCategory.congr_hom (NatTrans.congr_app a.inv_hom_id (Opposite.op ⦋0⦌)) x
  · rw [Category.assoc, h, ← Category.assoc, hlp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv l)).map ((truncation 2).map a.hom)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (l ≫ a.hom))).edge from
          SSet.yonedaEquiv_comp l a.hom)).1 (hli.map a.hom)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
