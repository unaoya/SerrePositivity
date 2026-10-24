module
public import SerrePositivity.InfinityCategories.Core.UniverseJoinAugmentation

/-! # 単体集合の join と宇宙の持ち上げの可換性

概要：join の ULift と二因子の ULift の join は実単体的同型。
方針：切断を保って空単体を含む両因子を上げ下げする。
規約：モデル構造は使わない。使われ方：普遍錐の宇宙降下。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet

/-- join の単体を二因子の宇宙を上げた join の単体へ送る。 -/
def uliftJoinSimplexUp (K L : SSet.{u}) {n : ℕ} (s : Join.Simplex K L n) :
    Join.Simplex ((SSet.uliftFunctor.{v, u}).obj K) ((SSet.uliftFunctor.{v, u}).obj L) n :=
  ⟨s.1, uliftJoinAugUp K _ s.2.1, uliftJoinAugUp L _ s.2.2⟩

/-- 二因子の宇宙を上げた join の単体を元へ戻す。 -/
def uliftJoinSimplexDown (K L : SSet.{u}) {n : ℕ}
    (s : Join.Simplex ((SSet.uliftFunctor.{v, u}).obj K)
      ((SSet.uliftFunctor.{v, u}).obj L) n) : Join.Simplex K L n :=
  ⟨s.1, uliftJoinAugDown K _ s.2.1, uliftJoinAugDown L _ s.2.2⟩

/-- join の単体の上げ操作は全ての単調写像と可換。 -/
lemma uliftJoinSimplexUp_map (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex K L n) :
    uliftJoinSimplexUp.{u, v} K L (Join.simplexMap K L α s) =
      Join.simplexMap ((SSet.uliftFunctor.{v, u}).obj K)
        ((SSet.uliftFunctor.{v, u}).obj L) α (uliftJoinSimplexUp K L s) := by
  rcases s with ⟨ℓ, x, y⟩
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact uliftJoinAugUp_map K _ x
  · exact uliftJoinAugUp_map L _ y

/-- join の単体の下げ操作は全ての単調写像と可換。 -/
lemma uliftJoinSimplexDown_map (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1))
    (s : Join.Simplex ((SSet.uliftFunctor.{v, u}).obj K)
      ((SSet.uliftFunctor.{v, u}).obj L) n) :
    uliftJoinSimplexDown K L
      (Join.simplexMap ((SSet.uliftFunctor.{v, u}).obj K)
        ((SSet.uliftFunctor.{v, u}).obj L) α s) =
      Join.simplexMap K L α (uliftJoinSimplexDown K L s) := by
  rcases s with ⟨ℓ, x, y⟩
  refine Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact uliftJoinAugDown_map K _ x
  · exact uliftJoinAugDown_map L _ y

/-- join の宇宙持ち上げは二因子の宇宙持ち上げと実同型で可換。 -/
def uliftJoinIso (K L : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj (join K L) ≅
      join ((SSet.uliftFunctor.{v, u}).obj K) ((SSet.uliftFunctor.{v, u}).obj L) where
  hom := {
    app _ := ↾fun s => uliftJoinSimplexUp K L s.down
    naturality _ _ α := by
      ext s
      exact uliftJoinSimplexUp_map K L α.unop.toOrderHom s.down }
  inv := {
    app _ := ↾fun s => ULift.up (uliftJoinSimplexDown K L s)
    naturality _ _ α := by
      ext s
      apply ULift.ext
      exact uliftJoinSimplexDown_map K L α.unop.toOrderHom s }
  hom_inv_id := by
    ext n s
    apply ULift.ext
    refine Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact uliftJoinAug_down_up K _ _
    · exact uliftJoinAug_down_up L _ _
  inv_hom_id := by
    ext n s
    refine Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact uliftJoinAug_up_down K _ _
    · exact uliftJoinAug_up_down L _ _

end SerrePositivity.InfinityCategories
