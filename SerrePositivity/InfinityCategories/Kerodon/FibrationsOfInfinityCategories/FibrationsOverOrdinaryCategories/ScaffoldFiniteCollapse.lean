module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCylinder

/-!
概要：有限鎖の零頂点と正の頂点を区間の両端へ送る射。
方針：零だけを零、他を一へ送る単調写像の nerve を標準区間へ移す。
規約：最初の辺は区間の恒等射へ、尾部は一頂点へ写る。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖上の比較を区間上の比較へ帰着する段階。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：有限鎖を零頂点と正の頂点の二群に分ける関手。
方針：零だけを零に送る単調写像を関手にする。
規約：標的の二点鎖も同じ宇宙に持ち上げる。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間への射の通常の圏での表示。 -/
def scaffoldFiniteCollapseFunctor (n : ℕ) :
    ULift.{u} (Fin (n + 2)) ⥤ ULift.{u} (Fin 2) :=
  (show ULift.{u} (Fin (n + 2)) →o ULift.{u} (Fin 2) from
    { toFun := fun i ↦ ULift.up (if i.down = 0 then 0 else 1)
      monotone' := by
        intro i j hij
        change (if i.down = 0 then (0 : Fin 2) else 1) ≤
          (if j.down = 0 then (0 : Fin 2) else 1)
        split_ifs with hi hj hj
        · exact le_rfl
        · decide
        · exfalso
          apply hi
          apply Fin.ext
          have h : i.down.val ≤ j.down.val := hij
          rw [hj] at h
          change i.down.val ≤ 0 at h
          exact Nat.eq_zero_of_le_zero h
        · exact le_rfl }).monotone.functor

/-- 概要：最初の辺への包含は区間への関手の切断。
方針：二つの頂点を計算し、順序圏の射の一意性を使う。
規約：厳密な関手の等式として述べる。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺を区間の恒等射として扱う。 -/
lemma scaffoldFiniteFirstEdge_collapse (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge.{u} n ⋙ scaffoldFiniteCollapseFunctor n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    rcases i with ⟨i⟩
    apply ULift.ext
    fin_cases i <;> rfl
  case h_map =>
    intro i j f
    exact Subsingleton.elim _ _

/-- 概要：尾部への包含の後に区間へ送ると一頂点に定値となる。
方針：後続元は零でないことを使う。
規約：全尾部を時刻一へ送る。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部が区間の一 fiber にあること。 -/
lemma scaffoldFiniteTail_collapse (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u} n ⋙ scaffoldFiniteCollapseFunctor n =
      (CategoryTheory.Functor.const _).obj (ULift.up (1 : Fin 2)) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    apply ULift.ext
    change (if i.down.succ = 0 then (0 : Fin 2) else 1) = 1
    rw [ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this)]
  case h_map =>
    intro i j f
    exact Subsingleton.elim _ _

/-- 概要：有限鎖の nerve を標準区間へ送る射。
方針：二点鎖への関手の nerve に標準区間との同型を合成する。
規約：零頂点以外を時刻一へ送る。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、全空間の区間への射影。 -/
def scaffoldFiniteCollapse (n : ℕ) :
    nerve (ULift.{u} (Fin (n + 2))) ⟶ (Δ[1] : SSet.{u}) :=
  nerveMap (scaffoldFiniteCollapseFunctor n) ≫ (stdSimplex.isoNerve 1).inv

/-- 概要：最初の辺は有限鎖から区間への射の切断。
方針：通常の関手の切断の等式を nerve へ移す。
規約：標準区間と二点鎖の nerve の標準同型を使う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺上の射影の計算。 -/
lemma scaffoldFiniteCollapse_firstEdge (n : ℕ) :
    (stdSimplex.isoNerve.{u} 1).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n) ≫
      scaffoldFiniteCollapse n = 𝟙 Δ[1] := by
  change (stdSimplex.isoNerve.{u} 1).hom ≫
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n ⋙ scaffoldFiniteCollapseFunctor n) ≫
      (stdSimplex.isoNerve 1).inv = _
  rw [scaffoldFiniteFirstEdge_collapse]
  change (stdSimplex.isoNerve.{u} 1).hom ≫ 𝟙 _ ≫ (stdSimplex.isoNerve 1).inv = _
  rw [Category.id_comp, Iso.hom_inv_id]

/-- 概要：有限鎖から区間への射は各頂点で零か正かを判定する。
方針：nerve と標準単体の同型の評価式を展開する。
規約：d 単体の頂点 i を明示する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間の fiber の同定。 -/
lemma scaffoldFiniteCollapse_app (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (i : Fin (d + 1)) :
    (scaffoldFiniteCollapse n).app (Opposite.op ⦋d⦌) σ i =
      if (σ.obj i).down = 0 then 0 else 1 := rfl

/-- 概要：有限鎖から区間への射は尾部全体を時刻一へ送る。
方針：各頂点が後続元であることから零への分岐を除く。
規約：右辺は時刻一の零単体への定値射。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部を区間の終点 fiber として扱う。 -/
lemma scaffoldFiniteCollapse_tail (n : ℕ) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u} n) ≫ scaffoldFiniteCollapse n =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (if (σ.obj i).down.succ = 0 then (0 : Fin 2) else 1).val = 1
  rw [ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this)]
  rfl

/-- 概要：有限鎖の零頂点は区間の始点へ写る。
方針：Yoneda 同値で零単体を計算する。
規約：区間の始点包含は δ₁。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、始点 fiber の同定。 -/
lemma scaffoldFiniteCollapse_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 2)) : ULift.{u} _) ≫ scaffoldFiniteCollapse n =
      stdSimplex.δ (1 : Fin 2) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (if (0 : Fin (n + 2)) = 0 then (0 : Fin 2) else 1).val =
    ((1 : Fin 2).succAbove (σ i)).val
  rw [ite_eq_left rfl]
  have hs : σ i = 0 := Fin.ext (by have := (σ i).isLt; omega)
  rw [hs]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
