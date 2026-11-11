module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareVertices

/-!
概要：底の同型による射影の後合成は四角形空間の厳密な同型を与える。
方針：全空間側の射を保ち分類図式だけを底の射で前合成する。
規約：底側と全空間側の射を同時に保持する。
使われ方：点との積の底を区間や境界へ移す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底の射で分類図式を前合成した四角形。
方針：全空間の射を変えず可換性を射影の後合成の等式で戻す。
規約：底の射の同値性は要求しない。
使われ方：底の同型による四角形の比較の頂点作用。 -/
def LeftTransportSquare.basePre {E B D : SSet.{u + 1}} {p : E ⟶ B} {q : E ⟶ D}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare q) (f : B ⟶ D) (hf : p ≫ f = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare p :=
  ⟨f ≫ S.diagram, S.pointedMap, S.comm.trans
    ((congrArg (fun g ↦ g ≫ S.diagram) hf).symm.trans (Category.assoc p f S.diagram))⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportSquare (basePre)


/-- 概要：底の射で前合成する四角形空間の射。
方針：分類図式の内部 Hom の前合成と不変の全空間の図式を束ねる。
規約：全高次単体の射。
使われ方：底を同型で移した四角形空間の比較。 -/
def transportSquareBasePre {E B D : SSet.{u + 1}} (p : E ⟶ B) (q : E ⟶ D)
    (f : B ⟶ D) (hf : p ≫ f = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition, Category.assoc, ← NatTrans.comp_app, ← pre_map, hf])

/-- 概要：底の前合成は全空間側の図式を変えない。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：底の同型で表現を移すときの全空間側の固定。 -/
lemma transportSquareBasePre_pointed {E B D : SSet.{u + 1}} (p : E ⟶ B) (q : E ⟶ D)
    (f : B ⟶ D) (hf : p ≫ f = q) :
    transportSquareBasePre p q f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q :=
  pullback.lift_fst _ _ _

/-- 概要：底の前合成は分類図式の指定した前合成を回収する。
方針：引き戻しへの lift の第二射影。
規約：厳密な射の一致。
使われ方：底の同型による分類図式の比較。 -/
lemma transportSquareBasePre_diagram {E B D : SSet.{u + 1}} (p : E ⟶ B) (q : E ⟶ D)
    (f : B ⟶ D) (hf : p ≫ f = q) :
    transportSquareBasePre p q f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := pullback.lift_snd _ _ _

/-- 概要：底の同型で射影を移した四角形の空間は元の四角形空間と同型。
方針：同型と逆同型で分類図式を前合成し二射影で往復を確認する。
規約：全空間は同じまま底だけを変更する。
使われ方：Δ⁰ と単体集合の積を元の単体集合の底へ移す。 -/
def transportSquareBaseIso {E B D : SSet.{u + 1}} (p : E ⟶ B) (q : E ⟶ D)
    (e : B ≅ D) (he : p ≫ e.hom = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace q ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p := by
  have hi : q ≫ e.inv = p := by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine { hom := transportSquareBasePre p q e.hom he
           inv := transportSquareBasePre q p e.inv hi
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed q = _
      rw [Category.assoc, transportSquareBasePre_pointed, transportSquareBasePre_pointed,
        Category.id_comp]
      rfl
    · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q = _
      rw [Category.assoc, transportSquareBasePre_diagram, ← Category.assoc,
        transportSquareBasePre_diagram, Category.assoc, ← NatTrans.comp_app, ← pre_map,
        Iso.inv_hom_id, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
      rfl
  · apply pullback.hom_ext
    · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p = _
      rw [Category.assoc, transportSquareBasePre_pointed, transportSquareBasePre_pointed,
        Category.id_comp]
      rfl
    · change (_ ≫ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p = _
      rw [Category.assoc, transportSquareBasePre_diagram, ← Category.assoc,
        transportSquareBasePre_diagram, Category.assoc, ← NatTrans.comp_app, ← pre_map,
        Iso.hom_inv_id, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]
      rfl

/-- 概要：底の前合成は頂点で実際の四角形の前合成を回収する。
方針：二射影の関手頂点を比較する。
規約：全空間側の図式も同時に保つ。
使われ方：表現条件の全部分複体への比較の制限。 -/
lemma transportSquareBasePre_vertex {E B D : SSet.{u + 1}} {p : E ⟶ B} {q : E ⟶ D}
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare q) (f : B ⟶ D) (hf : p ≫ f = q) :
    (transportSquareBasePre p q f hf).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex (S.basePre f hf) := by
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback ((ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
      ((pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).app (Opposite.op ⦋0⦌))
  · change (transportSquareBasePre p q f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquareBasePre_pointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_pointed (S.basePre f hf)).symm
  · change (transportSquareBasePre p q f hf ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S) = _
    rw [transportSquareBasePre_diagram]
    change ((pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram q).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex S)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex_diagram (S.basePre f hf)).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
