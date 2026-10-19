module
public import SerrePositivity.KST.SConstruction.SimplexFiberDiagram
public import SerrePositivity.KST.SConstruction.ElementsResolution

/-! # 左 fiber 解消の各係数次数の要素の圏の座標
概要：要素の圏の対象を元の X の単体と因子分解パラメーターとして読む。
方針：strict pullback の二射影と単体圏の射の保存則を使う。
規約：係数次数は固定し、元の単体を変更しない。使われ方：解消の augmentation の縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：左 fiber 図式の固定した係数次数の集合値図式。
方針：二変数を交換して指定次数で評価する。
規約：底は単体圏の反対圏。使われ方：解消の各行の要素の圏。 -/
abbrev fiberResolutionCoefficient {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (simplexFiberDiagram f).flip.obj (Opposite.op ⦋n⦌)

/-- 概要：係数次数 n の因子分解の要素の圏。
方針：集合値係数の要素の圏を取る。
規約：後で反対圏の nerve を解消の行に使う。使われ方：単体ごとの標準対象への比較。 -/
abbrev fiberResolutionCategory {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (fiberResolutionCoefficient f n).Elements

/-- 概要：因子分解対象の元の X の単体。
方針：左 fiber の第一射影。
規約：係数次数 n を保持。使われ方：解消の augmentation。 -/
def fiberResolutionValue {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) : X _⦋n⦌ :=
  (simplexLeftFiberProjection f e.obj.unop.val).app (Opposite.op ⦋n⦌) e.val

/-- 概要：因子分解対象の標準単体パラメーター。
方針：左 fiber の第二射影。
規約：頂点ラベルの次元を保持。使われ方：標準対象からの射の構成。 -/
def fiberResolutionParameter {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) :
    (stdSimplex.obj e.obj.unop.obj.unop).obj (Opposite.op ⦋n⦌) :=
  (simplexLeftFiberParameter f e.obj.unop.val).app (Opposite.op ⦋n⦌) e.val

/-- 概要：元の単体の f 像はラベル単体の指定パラメーターでの制限。
方針：strict pullback の可換性。
規約：元の n 単体の等号。使われ方：因子分解の標準射のラベル条件。 -/
lemma fiberResolution_condition {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) :
    f.app (Opposite.op ⦋n⦌) (fiberResolutionValue f e) =
      Y.map (stdSimplex.objEquiv (fiberResolutionParameter f e)).op e.obj.unop.val := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (simplexLeftFiber_condition f e.obj.unop.val) (Opposite.op ⦋n⦌)) e.val
  change _ = (SSet.yonedaEquiv.symm e.obj.unop.val).app (Opposite.op ⦋n⦌)
    (fiberResolutionParameter f e) at h
  rw [SSet.yonedaEquiv_symm_app] at h
  exact h

/-- 概要：因子分解の射は元の X の単体を保持する。
方針：要素の圏のラベル条件と左 fiber の第一射影の自然性。
規約：全ての単体圏の射。使われ方：augmentation の離散値の関手性。 -/
lemma fiberResolutionValue_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    {e d : fiberResolutionCategory f n} (h : e ⟶ d) :
    fiberResolutionValue f e = fiberResolutionValue f d := by
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (simplexFiberDiagramMap_projection f h.hom) (Opposite.op ⦋n⦌)) e.val
  have hv := congrArg (fun s =>
    (simplexLeftFiberProjection f d.obj.unop.val).app (Opposite.op ⦋n⦌) s) h.map_val
  exact hp.symm.trans hv

/-- 概要：因子分解の射の標準パラメーターは単体の射との後合成。
方針：要素の圏のラベル条件と左 fiber の第二射影の自然性。
規約：元のパラメーターの等号。使われ方：標準対象への射の一意性。 -/
lemma fiberResolutionParameter_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    {e d : fiberResolutionCategory f n} (h : e ⟶ d) :
    fiberResolutionParameter f d =
      (stdSimplex.map h.hom.unop.hom.unop).app (Opposite.op ⦋n⦌)
        (fiberResolutionParameter f e) := by
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (simplexFiberDiagramMap_parameter f h.hom) (Opposite.op ⦋n⦌)) e.val
  have hv := congrArg (fun s =>
    (simplexLeftFiberParameter f d.obj.unop.val).app (Opposite.op ⦋n⦌) s) h.map_val
  exact hv.symm.trans hp

end SerrePositivity.KST.SConstruction
