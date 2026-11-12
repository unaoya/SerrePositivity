module
public import SerrePositivity.KST.SConstruction.SimplexLeftFiber

/-! # object S の定値添字制限と最後の対角零対象
概要：添字を一定に制限した gapped 図式は、その対角頂点への定値図式となる。
方針：Ar の定値順序写像の nerve を計算する。
規約：元の gapped 図式の対角頂点を使う。使われ方：McCarthy の左 fiber の切断。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：定値な区間の添字写像の nerve は対角頂点への定値射。
方針：順序圏の nerve の単体は全ての頂点で決まる。
規約：始域の次数を自由に取る。使われ方：object S の定値制限。 -/
lemma arNerveMap_const (n m : ℕ) (i : Fin (m + 1)) :
    arNerveMap.{u} (OrderHom.const (Fin (n + 1)) i) =
      (SSet.const (ComposableArrows.mk₀ (arObj i i le_rfl)) : arNerve n ⟶ arNerve m) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  rfl

/-- 概要：object S の定値添字での制限は対角頂点への定値図式。
方針：実際の Ar 図式の制限の式と定値 nerve の式を使う。
規約：quasicategory 性を要求しない。使われ方：固定単体の最後の対角の選択。 -/
lemma gappedDiagram_objectS_const {C : SSet.{u}} {m n : ℕ}
    (v : (objectSConstruction C) _⦋m⦌) (i : Fin (m + 1)) :
    gappedDiagram ((objectSConstruction C).map (SimplexCategory.const ⦋n⦌ ⦋m⦌ i).op v) =
      (SSet.const ((gappedDiagram v).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj i i le_rfl))) : arNerve n ⟶ C) := by
  rw [gappedDiagram_objectS_map]
  change arNerveMap (OrderHom.const (Fin (n + 1)) i) ≫ gappedDiagram v = _
  rw [arNerveMap_const, SSet.const_comp]

/-- 概要：固定した object S の単体の最後の対角は実際の零対象。
方針：元の gapped 条件の対角の零対象性を取り出す。
規約：別の零対象への置換をしない。使われ方：左 fiber の切断に使う零射の自然変換。 -/
def objectSLastDiagonalZeroVertex {C : SSet.{u}} {m : ℕ}
    (a : (objectSConstruction C) _⦋m⦌) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex C :=
  ⟨(gappedDiagram a).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (arObj (Fin.last m) (Fin.last m) le_rfl)),
    ((gappedDiagram_isGapped a).1 (Fin.last m)).1,
    ((gappedDiagram_isGapped a).1 (Fin.last m)).2⟩

/-- 概要：指定零対象への定値完全関手を安定な入力間の射にする。
方針：零対象と全押し出しの保存を添える。
規約：底の射は厳密に定値射。使われ方：fiber の切断の基底の等式。 -/
def stableConstantZero (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier) : X ⟶ X :=
  ⟨SSet.const z.vertex, (constantZero_preservesSConstructionData z).toCofiberData⟩

/-- 概要：object S の単体を最後の頂点に制限する射は最後の対角零対象への定値関手の像。
方針：各単体の Ar 図式を計算して一致させる。
規約：固定した単体に依存する零対象を使う。使われ方：McCarthy の左 fiber の厳密な切断。 -/
lemma objectS_lastVertex_constantZero (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m)) :
      objectSConstruction X.carrier ⟶ Δ[m]) ≫ SSet.yonedaEquiv.symm a =
      objectSConstructionFunctor.map (stableConstantZero X (objectSLastDiagonalZeroVertex a)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  apply gappedDiagram_injective
  have hr : gappedDiagram
      ((objectSConstructionFunctor.map
        (stableConstantZero X (objectSLastDiagonalZeroVertex a))).app (Opposite.op ⦋n⦌) v) =
      SSet.const (objectSLastDiagonalZeroVertex a).vertex :=
    (gappedDiagram_objectSFunctor_map
      (stableConstantZero X (objectSLastDiagonalZeroVertex a)) (Opposite.op ⦋n⦌) v).trans
        (SSet.comp_const _ _)
  refine Eq.trans ?_ hr.symm
  change gappedDiagram
    ((SSet.yonedaEquiv.symm a).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last m)) n)) =
        SSet.const (objectSLastDiagonalZeroVertex a).vertex
  change gappedDiagram ((objectSConstruction X.carrier).map
    (SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)).op a) = _
  exact gappedDiagram_objectS_const a (Fin.last m)

end SerrePositivity.KST.SConstruction
