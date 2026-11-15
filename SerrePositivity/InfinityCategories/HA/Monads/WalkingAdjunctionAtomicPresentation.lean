module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicFaithful

/-!
概要：原子的な自由な道と各次数の実全射の圏の相互逆な実関手を構成する。
方針：検証した完全忠実な比較から逆を取り、両方向の全関手の等式を確認する。
規約：自由性を存在の仮定にしない。退化との両立は別に扱う。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の各次数の自由な表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実射の原子的な語を実際の道に展開する。
方針：検証済みの語の存在から選ぶ。規約：元の二対象を保持する。
使われ方：Riehl–Verity Proposition 3.1.10 の各次数の逆表示。 -/
def walkingAdjunctionAtomicWordPath {n : ℕ} {X Y : WalkingAdjunctionLevel n} (f : X ⟶ Y) :
    Quiver.Path (V := WalkingAdjunctionAtomicVertex n) ⟨X⟩ ⟨Y⟩ :=
  (Classical.choice (walkingAdjunctionAtomicWord_nonempty f)).toPath

/-- 概要：選んだ原子的な道の像は元の実射そのもの。
方針：語の道への展開の照合を使う。規約：全射を保持する。
使われ方：Riehl–Verity Proposition 3.1.10 の逆表示の検収。 -/
lemma walkingAdjunctionAtomicWordPath_map {n : ℕ} {X Y : WalkingAdjunctionLevel n} (f : X ⟶ Y) :
    (walkingAdjunctionAtomicPathFunctor n).map (walkingAdjunctionAtomicWordPath f) = f :=
  (Classical.choice (walkingAdjunctionAtomicWord_nonempty f)).toPath_map

/-- 概要：各次数の実全射を原子的な自由な道へ戻す実関手。
方針：語からの道を取り、法則を忠実性で戻す。
規約：同じ二対象を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionAtomicInverse (n : ℕ) :
    WalkingAdjunctionLevel n ⥤ Paths (WalkingAdjunctionAtomicVertex n) where
  obj X := ⟨X⟩
  map f := walkingAdjunctionAtomicWordPath f
  map_id X := by
    apply (walkingAdjunctionAtomicPathFunctor n).map_injective
    exact (walkingAdjunctionAtomicWordPath_map (𝟙 X)).trans
      ((walkingAdjunctionAtomicPathFunctor n).map_id _).symm
  map_comp f g := by
    apply (walkingAdjunctionAtomicPathFunctor n).map_injective
    calc
      _ = f ≫ g := walkingAdjunctionAtomicWordPath_map (f ≫ g)
      _ = (walkingAdjunctionAtomicPathFunctor n).map (walkingAdjunctionAtomicWordPath f) ≫
          (walkingAdjunctionAtomicPathFunctor n).map (walkingAdjunctionAtomicWordPath g) :=
        congrArg₂ (fun a b => a ≫ b)
          (walkingAdjunctionAtomicWordPath_map f).symm (walkingAdjunctionAtomicWordPath_map g).symm
      _ = _ := ((walkingAdjunctionAtomicPathFunctor n).map_comp _ _).symm

/-- 概要：自由な道を実全射へ合成して戻すと、元の全ての道を保つ。
方針：完全忠実な比較の原像の法則を使う。
規約：全関手そのものの等式。使われ方：Riehl–Verity Proposition 3.1.10 の各次数の自由性。 -/
lemma walkingAdjunctionAtomic_path_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicPathFunctor n ⋙ walkingAdjunctionAtomicInverse n =
      𝟭 (Paths (WalkingAdjunctionAtomicVertex n)) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y f
  apply heq_of_eq
  apply (walkingAdjunctionAtomicPathFunctor n).map_injective
  exact walkingAdjunctionAtomicWordPath_map ((walkingAdjunctionAtomicPathFunctor n).map f)

/-- 概要：実全射を自由な道に戻して合成すると、元の全ての射を保つ。
方針：完全性の原像の実像の法則を使う。
規約：全関手そのものの等式。使われ方：Riehl–Verity Proposition 3.1.10 の各次数の自由性。 -/
lemma walkingAdjunctionAtomic_level_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicInverse n ⋙ walkingAdjunctionAtomicPathFunctor n =
      𝟭 (WalkingAdjunctionLevel n) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y f
  exact heq_of_eq (walkingAdjunctionAtomicWordPath_map f)

end SerrePositivity.InfinityCategories.HA.Monads
