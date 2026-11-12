module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulFibration

/-!
概要：引き戻しの単体を一致する二つの単体で表示する。
方針：Yoneda 同値で引き戻しの普遍性を各次数の元へ移す。
規約：Mathlib の選ばれた引き戻しをそのまま使う。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の基底変換。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：一致する二つの単体から引き戻しの単体を作る。
方針：Yoneda 表示した二つの射を引き戻しへ持ち上げる。
規約：引き戻しの第一・第二射影を指定した順に使う。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の引き戻し。 -/
noncomputable def pullbackSimplex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback p q) _⦋n⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) (by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h]))

/-- 概要：作った引き戻しの単体の第一成分は指定した単体。
方針：引き戻しの第一射影の普遍性を Yoneda で読む。
規約：厳密な等式。
使われ方：Kerodon §4.8.4（Tag 06SQ） の引き戻しの各成分。 -/
lemma pullbackSimplex_fst {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback.fst p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h) = x := by
  rw [pullbackSimplex, ← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：作った引き戻しの単体の第二成分は指定した単体。
方針：引き戻しの第二射影の普遍性を Yoneda で読む。
規約：厳密な等式。
使われ方：Kerodon §4.8.4（Tag 06SQ） の引き戻しの各成分。 -/
lemma pullbackSimplex_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback.snd p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h) = y := by
  rw [pullbackSimplex, ← SSet.yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：引き戻しの単体は両方の射影で決まる。
方針：Yoneda 表示した射に引き戻しの普遍性を適用する。
規約：任意の次数。
使われ方：Kerodon §4.8.4（Tag 06SQ） の引き戻しの単体の自然性。 -/
lemma pullbackSimplex_ext {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    {x y : (pullback p q) _⦋n⦌}
    (hf : (pullback.fst p q).app (Opposite.op ⦋n⦌) x = (pullback.fst p q).app (Opposite.op ⦋n⦌) y)
    (hs : (pullback.snd p q).app (Opposite.op ⦋n⦌) x = (pullback.snd p q).app (Opposite.op ⦋n⦌) y) :
    x = y := by
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hf]
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hs]

/-- 概要：引き戻しの単体の両射影は標的で一致する。
方針：引き戻しの可換性を各次数で評価する。
規約：任意の次数。
使われ方：Kerodon §4.8.4（Tag 06SQ） の引き戻しの単体の再構成。 -/
lemma pullbackSimplex_compat {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : (pullback p q) _⦋n⦌) :
    p.app (Opposite.op ⦋n⦌) ((pullback.fst p q).app (Opposite.op ⦋n⦌) x) =
      q.app (Opposite.op ⦋n⦌) ((pullback.snd p q).app (Opposite.op ⦋n⦌) x) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := p) (g := q))
    (Opposite.op ⦋n⦌)) x

/-- 概要：引き戻しの単体を両射影から再構成すると元の単体。
方針：両射影を比較する。
規約：一致の証明の選択には依存しない。
使われ方：Kerodon §4.8.4（Tag 06SQ） の基底変換の往復。 -/
lemma pullbackSimplex_eta {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : (pullback p q) _⦋n⦌) :
    pullbackSimplex p q ((pullback.fst p q).app (Opposite.op ⦋n⦌) x)
      ((pullback.snd p q).app (Opposite.op ⦋n⦌) x) (pullbackSimplex_compat p q x) = x := by
  apply pullbackSimplex_ext p q
  · exact pullbackSimplex_fst _ _ _ _ _
  · exact pullbackSimplex_snd _ _ _ _ _

/-- 概要：引き戻しの単体の構成は単体作用と可換。
方針：両射影の自然性を使って二つの成分を比較する。
規約：新しい一致の証明は任意のものを使える。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の引き戻しの自然性。 -/
lemma pullbackSimplex_map {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n m : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y)
    (h' : p.app (Opposite.op ⦋m⦌) (X.map α.op x) = q.app (Opposite.op ⦋m⦌) (Y.map α.op y)) :
    (pullback p q).map α.op (pullbackSimplex p q x y h) =
      pullbackSimplex p q (X.map α.op x) (Y.map α.op y) h' := by
  apply pullbackSimplex_ext p q
  · rw [pullbackSimplex_fst]
    calc
      _ = X.map α.op ((pullback.fst p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h)) :=
        ConcreteCategory.congr_hom ((pullback.fst p q).naturality α.op) _
      _ = X.map α.op x := by rw [pullbackSimplex_fst]
  · rw [pullbackSimplex_snd]
    calc
      _ = Y.map α.op ((pullback.snd p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h)) :=
        ConcreteCategory.congr_hom ((pullback.snd p q).naturality α.op) _
      _ = Y.map α.op y := by rw [pullbackSimplex_snd]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
