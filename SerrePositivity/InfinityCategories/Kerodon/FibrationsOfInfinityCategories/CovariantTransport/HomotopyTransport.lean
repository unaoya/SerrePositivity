module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat

/-!
概要：cocartesian fibration の底のホモトピー圏上の covariant transport 表現。
方針：各 fiber と選択した辺の transport の同型類を恒等則・三角形の合成則で降下させる。
規約：標的は関手の同型類を射とする HomotopyQCat。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、F1b のホモトピー圏への降下。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：底の頂点に対応する fiber を quasicategory のホモトピー圏の対象にする。
方針：cocartesian fibration の fiber の quasicategory 性を束縛する。
規約：底の quasicategory 性はこの対象の構成には不要。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、transport 表現の対象への作用。 -/
def homotopyTransportFiber {X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat.{u} := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p b⟩

/-- 概要：cocartesian fibration の transport は底のホモトピー圏上の関手を定める。
方針：恒等辺の transport の恒等との同型と三角形の合成同型を商の等式にする。
規約：底は quasicategory、選択した transport の同型類を辺に対応させる。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、covariant homotopy transport representation。 -/
noncomputable def homotopyTransport {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] : hoFunctor.obj B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat.{u} := by
  apply SSet.Truncated.HomotopyCategory.lift (homotopyTransportFiber p)
    (fun {a b} e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk (X := homotopyTransportFiber p a)
      (Y := homotopyTransportFiber p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e))
  · intro b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk_eq_of_functorIso
      (X := homotopyTransportFiber p b) (Y := homotopyTransportFiber p b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_identity_iso p b)
  · intro a b c e f g σ
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk_eq_of_functorIso
      (X := homotopyTransportFiber p a) (Y := homotopyTransportFiber p c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_composition_iso p σ)).symm

/-- 概要：ホモトピー transport 表現は頂点をその fiber に写す。
方針：ホモトピー圏からの関手の構成の対象部分を計算する。
規約：頂点は標準の HomotopyCategory.mk で表示する。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、fiber の回収。 -/
lemma homotopyTransport_obj {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (b : B _⦋0⦌) :
    (homotopyTransport p).obj (SSet.HomotopyCategory.mk b) = homotopyTransportFiber p b := rfl

/-- 概要：ホモトピー transport 表現は辺を選択した transport 関手の同型類に写す。
方針：ホモトピー圏からの関手の生成元での計算則を使う。
規約：端点付き辺をホモトピー圏の生成射として表す。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、transport 表現の射への作用。 -/
lemma homotopyTransport_map_edge {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    (homotopyTransport p).map (SSet.HomotopyCategory.homMk e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk (X := homotopyTransportFiber p a)
        (Y := homotopyTransportFiber p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) :=
  Category.id_comp _

/-- 概要：任意の transport の証人はホモトピー transport 表現の同じ射を与える。
方針：生成辺での計算則と transport の証人の関手同型を使う。
規約：選択した関手との厳密な等式は要求しない。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、transport の選択からの独立性。 -/
lemma homotopyTransport_map_isTransport {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p e F) :
    (homotopyTransport p).map (SSet.HomotopyCategory.homMk e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk (X := homotopyTransportFiber p a)
        (Y := homotopyTransportFiber p b) F := by
  rw [homotopyTransport_map_edge]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk_eq_of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.functorIso p e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e) hF)

/-- 概要：fiber と辺の transport の同型類でホモトピー transport 表現は一意に決まる。
方針：ホモトピー圏の生成辺に関する関手の外延性を使う。
規約：対象の等式に伴う射の型の変更は eqToHom で明示する。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、transport 表現の特徴づけ。 -/
lemma homotopyTransport_unique {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (T : hoFunctor.obj B ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HomotopyQCat.{u})
    (hobj : ∀ b : B _⦋0⦌, T.obj (SSet.HomotopyCategory.mk b) = homotopyTransportFiber p b)
    (hmap : ∀ {a b : B _⦋0⦌}
      (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b),
      T.map (SSet.HomotopyCategory.homMk e) = eqToHom (hobj a) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk (X := homotopyTransportFiber p a)
          (Y := homotopyTransportFiber p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ≫ eqToHom (hobj b).symm) :
    T = homotopyTransport p := by
  apply SSet.Truncated.HomotopyCategory.functor_ext hobj
  intro a b e
  have h : (homotopyTransport p).map (SSet.Truncated.HomotopyCategory.homMk e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.homotopyQCatHomMk (X := homotopyTransportFiber p a)
        (Y := homotopyTransportFiber p b) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) :=
    homotopyTransport_map_edge p e
  rw [h]
  exact hmap e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
