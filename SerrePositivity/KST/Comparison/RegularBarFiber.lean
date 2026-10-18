module

public import SerrePositivity.KST.Comparison.RegularBarContraction
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 正則 bar の厳密ファイバー

概要：正則 bar の射影の基点上の厳密ファイバーをモノイドと同定する。
方針：射影の全てのラベルが単位なら正則作用の射列は定数となる。
規約：Segal 1974 Proposition 1.5 のファイバー比較の厳密側。ホモトピーファイバーとは区別する。
使われ方：群状性を使う普遍 bar 束の比較の始域。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：正則 bar の射影の基点上の厳密ファイバーを部分単体集合として定義する。
方針：各次数で射影が基点の退化単体に一致することを要求する。
規約：Segal 1974 Proposition 1.5。群状性は使わない。
使われ方：M から厳密ファイバーへの標準同型。
-/
def regularBarStrictFiber (M : SimplicialObject MonCat.{u}) : (regularBar M).Subcomplex where
  obj n := {E | (regularBarProjection M).app n E =
    (monoidBar M).map (SimplexCategory.const n.unop ⦋0⦌ 0).op (monoidBarBasepoint M)}
  map {i j} f E h := by
    change ((regularBar M).map f ≫ (regularBarProjection M).app j) E = _
    rw [(regularBarProjection M).naturality f]
    change (monoidBar M).map f ((regularBarProjection M).app i E) = _
    rw [h, ← Functor.map_comp_apply]
    congr 1

/--
概要：M の標準写像を基点上の厳密ファイバーへ持ち上げる。
方針：射影との合成が基点に定数である三角形を使う。
規約：Segal 1974 Proposition 1.5。厳密な因子化。
使われ方：ファイバー同型の順方向。
-/
def regularBarFiberLift (M : SimplicialObject MonCat.{u}) :
    monoidSpace M ⟶ (regularBarStrictFiber M : SSet.{u}) :=
  SSet.Subcomplex.lift (regularBarFiberMap M) (by
    rintro n E ⟨m, rfl⟩
    exact congrArg (fun k => k.app n m) (regularBarFiberMap_projection M))

/--
概要：厳密ファイバーの射列の全ての射のラベルは単位である。
方針：射影の等式を各射で評価する。
規約：Segal 1974 Proposition 1.5 の正則 bar 束。
使われ方：ファイバーの射列が定数であること。
-/
theorem regularBarStrictFiber_label (M : SimplicialObject MonCat.{u})
    (n : SimplexCategoryᵒᵖ) (E : (regularBarStrictFiber M).obj n)
    {i j : Fin (n.unop.len + 1)} (f : i ⟶ j) : (E.val.map f).val = 1 := by
  have he : E.val ⋙ regularActionProjection (M.obj n) =
      (SimplexCategory.toCat.map (SimplexCategory.const n.unop ⦋0⦌ 0)).toFunctor ⋙
        (Functor.const (Fin 1)).obj (SingleObj.star (M.obj (op ⦋0⦌))) ⋙
          SingleObj.mapHom _ _ (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom := E.property
  have hf := congrArg (fun F : Fin (n.unop.len + 1) ⥤ SingleObj (M.obj n) =>
    (show M.obj n from F.map f)) he
  exact hf.trans (map_one _)

/--
概要：厳密ファイバーの射列の全ての対象はその始点に一致する。
方針：始点からの射の条件に単位ラベルの等式を代入する。
規約：Segal 1974 Proposition 1.5。逆元も群状性も不要。
使われ方：ファイバー同型の逆写像の証明。
-/
theorem regularBarStrictFiber_obj (M : SimplicialObject MonCat.{u})
    (n : SimplexCategoryᵒᵖ) (E : (regularBarStrictFiber M).obj n)
    (i : Fin (n.unop.len + 1)) : (E.val.obj 0).val = (E.val.obj i).val := by
  have h := (E.val.map (homOfLE (Fin.zero_le i))).property
  rw [regularBarStrictFiber_label M n E, one_mul] at h
  exact h
/--
概要：標準ファイバー写像は各単体次数で全単射である。
方針：始点の値を逆写像とし、単位ラベルから射列が定数であることを示す。
規約：Segal 1974 Proposition 1.5 の厳密ファイバーの同定。
使われ方：M と基点上の厳密ファイバーの単体的同型。
-/
theorem regularBarFiberLift_bijective (M : SimplicialObject MonCat.{u})
    (n : SimplexCategoryᵒᵖ) : Function.Bijective ((regularBarFiberLift M).app n) := by
  constructor
  · intro a b h
    exact congrArg (fun E : (regularBarStrictFiber M).obj n => (E.val.obj 0).val) h
  · intro E
    refine ⟨(E.val.obj 0).val, Subtype.ext ?_⟩
    change (Functor.const (Fin (n.unop.len + 1))).obj (RegularAction.mk (E.val.obj 0).val) = E.val
    refine CategoryTheory.Functor.ext (fun i => ?_) ?_
    · exact congrArg RegularAction.mk (regularBarStrictFiber_obj M n E i)
    · intro i j f
      apply Subtype.ext
      simp only [regularAction_comp_val, regularAction_eqToHom_val, one_mul, mul_one]
      change (1 : M.obj n) = (E.val.map f).val
      exact (regularBarStrictFiber_label M n E f).symm

/--
概要：正則 bar の基点上の厳密ファイバーは M と単体的に同型である。
方針：標準写像の次数ごとの全単射と既存の自然性を束ねる。
規約：Segal 1974 Proposition 1.5。ホモトピーファイバー比較の前段。
使われ方：bar 射影のファイバーの入口を具体化する。
-/
noncomputable def regularBarFiberIso (M : SimplicialObject MonCat.{u}) :
    monoidSpace M ≅ (regularBarStrictFiber M : SSet.{u}) :=
  NatIso.ofComponents
    (fun n => (Equiv.ofBijective ((regularBarFiberLift M).app n)
      (regularBarFiberLift_bijective M n)).toIso)
    (fun {_ _} f => (regularBarFiberLift M).naturality f)

/--
概要：M、正則 bar、基点、分類空間の標準四角形は引き戻しである。
方針：各単体次数の厳密ファイバーの全単射を引き戻しの普遍性へ移す。
規約：Segal 1974 Proposition 1.5。ホモトピー引き戻し性は別途必要。
使われ方：普遍 bar 束の厳密ファイバーの標準四角形。
-/
theorem regularBarFiber_isPullback (M : SimplicialObject MonCat.{u}) :
    IsPullback (regularBarFiberMap M)
      (SSet.stdSimplex.isTerminalObj₀.from (monoidSpace M))
      (regularBarProjection M) (SSet.yonedaEquiv.symm (monoidBarBasepoint M)) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    have h := congrArg (fun k => k.app n a) (regularBarFiberMap_projection M)
    exact h
  · intro a b h
    exact congrArg (fun E : (regularBar M).obj n => (E.obj 0).val) h.1
  · intro E z hz
    have hmem : E ∈ (regularBarStrictFiber M).obj n := by
      change (regularBarProjection M).app n E = _
      rw [hz, SSet.yonedaEquiv_symm_app]
      exact congrArg (fun f : op ⦋0⦌ ⟶ n => (monoidBar M).map f (monoidBarBasepoint M))
        (Subsingleton.elim _ _)
    obtain ⟨a, ha⟩ := (regularBarFiberLift_bijective M n).surjective ⟨E, hmem⟩
    refine ⟨a, congrArg Subtype.val ha, ?_⟩
    apply SSet.stdSimplex.objEquiv.injective
    apply Subsingleton.elim


end SerrePositivity.KST.Comparison
