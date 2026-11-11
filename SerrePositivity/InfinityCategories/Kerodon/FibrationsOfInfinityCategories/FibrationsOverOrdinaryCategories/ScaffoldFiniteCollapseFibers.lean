module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCollapse
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：有限鎖から区間への射の両端 fiber の厳密な表示。
方針：各次数で零の射列と正の射列を分け、正の射列を尾部で一意に因子化する。
規約：fiber は単体集合の pullback として与える。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の比較の両端条件。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：区間の始点に写る有限鎖の単体は零頂点に定値。
方針：各頂点で零以外の分岐が時刻一へ写ることを使う。
規約：始点の零単体の任意の退化単体との等式から結論する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、始点 fiber の単体ごとの計算。 -/
lemma scaffoldFiniteCollapse_zero_obj (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (x : (Δ[0] : SSet.{u}) _⦋d⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n).app _ σ = (stdSimplex.δ (1 : Fin 2)).app _ x)
    (i : Fin (d + 1)) : (σ.obj i).down = 0 := by
  have hi := congrArg (fun s : (Δ[1] : SSet.{u}) _⦋d⦌ ↦ (s i).val) h
  change (if (σ.obj i).down = 0 then (0 : Fin 2) else 1).val =
    ((1 : Fin 2).succAbove (x i)).val at hi
  have hx : x i = 0 := Fin.ext (by have := (x i).isLt; omega)
  rw [hx] at hi
  by_contra hz
  simp [hz] at hi

/-- 概要：区間の終点に写る有限鎖の単体は零頂点を避ける。
方針：零頂点が時刻零に写るという計算を用いて矛盾させる。
規約：最初の頂点だけでなく任意の頂点を扱う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部への因子化の前提。 -/
lemma scaffoldFiniteCollapse_one_obj (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (x : (Δ[0] : SSet.{u}) _⦋d⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n).app _ σ = (stdSimplex.δ (0 : Fin 2)).app _ x)
    (i : Fin (d + 1)) : (σ.obj i).down ≠ 0 := by
  intro hz
  have hi := congrArg (fun s : (Δ[1] : SSet.{u}) _⦋d⦌ ↦ (s i).val) h
  change (if (σ.obj i).down = 0 then (0 : Fin 2) else 1).val =
    ((0 : Fin 2).succAbove (x i)).val at hi
  rw [hz, ite_eq_left rfl, Fin.succAbove_zero] at hi
  have hx : x i = 0 := Fin.ext (by have := (x i).isLt; omega)
  rw [hx] at hi
  contradiction

/-- 概要：有限鎖から区間への射の零 fiber は零頂点そのもの。
方針：各次数の pullback の持ち上げを定値零の射列で一意に与える。
規約：零 fiber の底への射は標準零単体の恒等射。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、零 fiber の係数との比較。 -/
lemma scaffoldFiniteCollapse_zero_isPullback (n : ℕ) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 2)) : ULift.{u} _))
      (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.δ (1 : Fin 2)) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 2)) : ULift.{u} _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n =
      𝟙 Δ[0] ≫ stdSimplex.δ (1 : Fin 2) := by
    rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse_zero]
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨congrArg (fun f ↦ f.app d) hc, ?_, ?_⟩
  · intro x y h
    exact h.2
  · intro σ x h
    refine ⟨x, ?_, rfl⟩
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    change ULift.up (0 : Fin (n + 2)) = σ.obj i
    exact ULift.ext (scaffoldFiniteCollapse_zero_obj n d.unop.len σ x h i).symm

/-- 概要：有限鎖から区間への射の一 fiber は尾部の nerve。
方針：正の射列を一ずつ下げて尾部へ戻し、後者写像の単射性で一意性を示す。
規約：尾部から標準零単体への射は唯一の射。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の帰納仮定を終点 fiber に適用する。 -/
lemma scaffoldFiniteCollapse_one_isPullback (n : ℕ) :
    IsPullback (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u} n))
      (stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin (n + 1)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.δ (0 : Fin 2)) := by
  have hc : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail.{u} n) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n =
      stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ (0 : Fin 2) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse_tail, stdSimplex.δ_zero_eq_const, SSet.comp_const]
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨congrArg (fun f ↦ f.app d) hc, ?_, ?_⟩
  · intro σ τ h
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    apply ULift.ext
    apply Fin.ext
    have hi := congrArg (fun s ↦ (s.obj i).down.val) h.1
    change (σ.obj i).down.val + 1 = (τ.obj i).down.val + 1 at hi
    omega
  · intro σ x h
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor σ, ?_, ?_⟩
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor_comp σ (scaffoldFiniteCollapse_one_obj n d.unop.len σ x h 0)
    · change (Δ[0] _⦋d.unop.len⦌ : Type u) at x
      let y : (Δ[0] : SSet.{u}) _⦋d.unop.len⦌ :=
        (stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin (n + 1))))).app d
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor σ)
      change y = x
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      have hx := (x i).isLt
      have hy := (y i).isLt
      omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
