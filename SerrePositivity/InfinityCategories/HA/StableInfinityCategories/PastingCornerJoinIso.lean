module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PastingCornerCocone

/-! # 長方形の終端角による join 表示

概要：五頂点図式と一点の join は長方形と同型である。
方針：終端角になる最初の頂点で各単体を切り、余錐の射の全射性を示す。
規約：長方形の終端角は (2,1)。使われ方：S4 の余極限の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：終端角だけを一に送る単調写像。
方針：有限順序集合の全ての比較を検査する。
規約：他の五頂点は零。使われ方：長方形の単体の切断位置。 -/
def pastingTerminalFlag : Fin 3 × Fin 2 →o Fin 2 where
  toFun v := if v = (2, 1) then 1 else 0
  monotone' := by decide

/-- 概要：終端角の旗が零であることは部分長方形に属することと同値。
方針：六頂点を検査する。
規約：番号の不等式で書く。使われ方：切断前の単体の所属条件。 -/
lemma pastingTerminalFlag_lt (x : Fin 3) (y : Fin 2) :
    (pastingTerminalFlag (x, y)).val < 1 ↔ (x = 2 → y ≠ 1) := by
  exact (by decide : ∀ x : Fin 3, ∀ y : Fin 2,
    (pastingTerminalFlag (x, y)).val < 1 ↔ (x = 2 → y ≠ 1)) x y

/-- 概要：各頂点で部分長方形に属する二つの順序写像から補った単体を作る。
方針：頂点数零なら空単体、それ以外なら標準単体の表現可能性を使う。
規約：r は頂点数。使われ方：長方形の単体の切断前の因子。 -/
def pastingAugOfCoords (r : ℕ) (x : Fin r →o Fin 3) (y : Fin r →o Fin 2)
    (h : ∀ i, x i = 2 → y i ≠ 1) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) r :=
  match r with
  | 0 => PUnit.unit
  | k + 1 => ⟨((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 2 (k + 1)).symm x,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 1 (k + 1)).symm y), h⟩

/-- 概要：二座標から作った補った単体の横座標を復元する。
方針：頂点数で場合分けする。規約：空単体も含む。
使われ方：余錐の全射性。 -/
lemma pastingAugOfCoords_x (r : ℕ) (x : Fin r →o Fin 3) (y : Fin r →o Fin 2)
    (h : ∀ i, x i = 2 → y i ≠ 1) (i : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingAugX r (pastingAugOfCoords r x y h) i = x i := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k => rfl

/-- 概要：二座標から作った補った単体の縦座標を復元する。
方針：頂点数で場合分けする。規約：空単体も含む。
使われ方：余錐の全射性。 -/
lemma pastingAugOfCoords_y (r : ℕ) (x : Fin r →o Fin 3) (y : Fin r →o Fin 2)
    (h : ∀ i, x i = 2 → y i ≠ 1) (i : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingAugY r (pastingAugOfCoords r x y h) i = y i := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k => rfl

/-- 概要：長方形への余錐の射は全次数で全射。
方針：終端角の旗を使って切断し、前半の二座標と後半の一点から join の単体を作る。
規約：全ての退化単体を含む。使われ方：長方形の join 同型。 -/
lemma pastingCornerCocone_app_surjective (d : ℕ) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone.{u}.app (Opposite.op ⦋d⦌)) := by
  intro s
  let x := (stdSimplex.objEquiv s.1).toOrderHom
  let y := (stdSimplex.objEquiv s.2).toOrderHom
  let flag : Fin (d + 1) →o Fin 2 := pastingTerminalFlag.comp (x.prod y)
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut flag 1
  have hr : r ≤ d + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le flag 1
  let incl : Fin r →o Fin (d + 1) := ⟨fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hr⟩,
    fun _ _ h ↦ h⟩
  have hcoords : ∀ i, (x.comp incl) i = 2 → (y.comp incl) i ≠ 1 := by
    intro i
    apply (pastingTerminalFlag_lt _ _).mp
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff flag 1 (incl i)).mp i.isLt
  let a := pastingAugOfCoords r (x.comp incl) (y.comp incl) hcoords
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 (d + 1 - r)).symm (OrderHom.const _ 0)
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] d :=
    ⟨⟨r, by omega⟩, a, b⟩
  refine ⟨t, ?_⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    by_cases hi : i.val < r
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_appX_of_lt t i hi]
      exact pastingAugOfCoords_x r _ _ hcoords ⟨i.val, hi⟩
    · have hf : ¬ (flag i).val < 1 := fun h ↦ hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff flag 1 i).mpr h)
      have hn := mt (pastingTerminalFlag_lt (x i) (y i)).mpr hf
      have hx : x i = 2 := by tauto
      exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_app_of_ge t i (Nat.le_of_not_gt hi)).1.trans hx.symm
  · apply stdSimplex.ext
    intro i
    by_cases hi : i.val < r
    · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_appY_of_lt t i hi]
      exact pastingAugOfCoords_y r _ _ hcoords ⟨i.val, hi⟩
    · have hf : ¬ (flag i).val < 1 := fun h ↦ hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff flag 1 i).mpr h)
      have hn := mt (pastingTerminalFlag_lt (x i) (y i)).mpr hf
      have hy : y i = 1 := by tauto
      exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_app_of_ge t i (Nat.le_of_not_gt hi)).2.trans hy.symm

/-- 概要：長方形への余錐の射は同型。
方針：各次数の単射性と全射性を使う。
規約：単体集合としての同型。使われ方：長方形上の余錐の表示。 -/
instance pastingCornerCocone_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone.{u}) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨d⟩⟩
  exact (isIso_iff_bijective _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_app_injective d, pastingCornerCocone_app_surjective d⟩

/-- 概要：五頂点図式と終端角の join は長方形に同型。
方針：二座標で構成した余錐の射を同型として束ねる。
規約：順方向は pastingCornerCocone。使われ方：S4 の貼り合わせの普遍性。 -/
def pastingCornerJoinIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] ≅ (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  asIso _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
