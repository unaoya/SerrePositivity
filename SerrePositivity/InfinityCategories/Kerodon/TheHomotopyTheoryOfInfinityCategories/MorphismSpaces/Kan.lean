module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomMono

/-!
概要：単体集合の宇宙の持ち上げによる Kan 性の保存。
方針：持ち上げたホーンの各面を Yoneda の同値で元の宇宙へ戻し、充填単体を持ち上げる。
規約：標準単体の宇宙も同時に変える。異なる宇宙間の単体集合の射は仮定しない。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、Theorem 4.6.7.5（Tag 01LE）、比較の始域の Kan 性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：持ち上げた単体集合の標準単体からの射を元の宇宙に戻す。
方針：Yoneda の同値の単体の ULift を外す。
規約：元の射の始域は大きい宇宙の標準単体。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較の Kan 性のための面の降下。 -/
def uliftSimplexHomDown {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X) :
    (Δ[n] : SSet.{u}) ⟶ X :=
  SSet.yonedaEquiv.symm (SSet.yonedaEquiv f).down

/-- 概要：単体の宇宙を戻す操作は面への制限と整合する。
方針：Yoneda の同値で面を評価し、ULift の成分の定義を計算する。
規約：全ての面番号を扱う。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、元の宇宙でのホーンの互換性。 -/
lemma uliftSimplexHomDown_face {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n + 1] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ uliftSimplexHomDown f =
      uliftSimplexHomDown (stdSimplex.δ j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  simp only [uliftSimplexHomDown, Equiv.apply_symm_apply,
    stdSimplex.yonedaEquiv_δ_comp]
  rfl

/-- 概要：Kan 複体の宇宙の持ち上げは Kan 複体。
方針：互換なホーン面を元の宇宙で充填し、その充填単体を持ち上げる。
規約：任意の追加宇宙 v に対して成立する。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、Theorem 4.6.7.5（Tag 01LE）、比較の始域。 -/
instance kanComplex_uliftFunctor_obj (X : SSet.{u}) [KanComplex X] :
    KanComplex (SSet.uliftFunctor.{v, u}.obj X) := by
  rw [KanComplex.iff]
  intro n i f hf
  have hF : horn.IsCompatible (fun j hj ↦ uliftSimplexHomDown (f j hj)) := by
    cases n with
    | zero => trivial
    | succ n =>
      intro j k hj hk hjk
      rw [uliftSimplexHomDown_face, uliftSimplexHomDown_face, hf j k hj hk hjk]
  obtain ⟨φ, hφ⟩ := hF.exists_lift_of_kanComplex
  refine ⟨SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv φ)), fun j hj ↦ ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change ULift.up (X.δ j (SSet.yonedaEquiv φ)) = SSet.yonedaEquiv (f j hj)
  apply ULift.ext
  have h := congrArg SSet.yonedaEquiv (hφ j hj)
  rw [stdSimplex.yonedaEquiv_δ_comp] at h
  simpa only [uliftSimplexHomDown, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
