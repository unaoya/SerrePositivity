module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEndpointPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：relative join の両端の頂点 fiber と元の因子との標準同型。
方針：両端の pullback と部分型で定義した頂点 fiber の pullback を同定する。
規約：順方向は因子から頂点 fiber へ。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、Theorem 5.2.4.1（Tag 024N）、全空間比較の両端条件。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：relative join の零 fiber は左因子と標準同型。
方針：同じ二射の pullback の一意性で二つの表示を結ぶ。
規約：構造射 f と g は任意。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、零 fiber の比較を元の係数に戻す。 -/
noncomputable def relativeJoinZeroFiberIso {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    X ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_endpoint_isPullback f g).isoPullback ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).isoPullback.symm

/-- 概要：零 fiber 同型の後に全空間へ含めると左包含になる。
方針：pullback の標準同型の第一射影を計算する。
規約：左因子の単体は保つ。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、零端の比較の式。 -/
lemma relativeJoinZeroFiberIso_hom_ι {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (relativeJoinZeroFiberIso f g).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f g := by
  simp only [relativeJoinZeroFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

/-- 概要：relative join の一 fiber は右因子と標準同型。
方針：同じ二射の pullback の一意性で二つの表示を結ぶ。
規約：構造射 f と g は任意。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、一 fiber の比較を元の係数に戻す。 -/
noncomputable def relativeJoinOneFiberIso {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_endpoint_isPullback f g).isoPullback ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).isoPullback.symm

/-- 概要：一 fiber 同型の後に全空間へ含めると右包含になる。
方針：pullback の標準同型の第一射影を計算する。
規約：右因子の単体は保つ。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、一端の比較の式。 -/
lemma relativeJoinOneFiberIso_hom_ι {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (relativeJoinOneFiberIso f g).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f g := by
  simp only [relativeJoinOneFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

/-- 概要：区間上の射の零 fiber の射は左因子の包含に沿って計算できる。
方針：fiber の誘導射の包含後の式と零 fiber 同型の計算則を使う。
規約：全空間の射は区間への射影を保つ。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、零端の比較と全体の比較の接続。 -/
lemma relativeJoinZeroFiberIso_vertexFiberMap_ι {X Y S E : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g ⟶ E) (hG : G ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) :
    (relativeJoinZeroFiberIso f g).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f g ≫ G := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, relativeJoinZeroFiberIso_hom_ι]

/-- 概要：区間上の射の一 fiber の射は右因子の包含に沿って計算できる。
方針：fiber の誘導射の包含後の式と一 fiber 同型の計算則を使う。
規約：全空間の射は区間への射影を保つ。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、一端の比較と全体の比較の接続。 -/
lemma relativeJoinOneFiberIso_vertexFiberMap_ι {X Y S E : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g ⟶ E) (hG : G ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) :
    (relativeJoinOneFiberIso f g).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f g) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f g ≫ G := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, relativeJoinOneFiberIso_hom_ι]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
