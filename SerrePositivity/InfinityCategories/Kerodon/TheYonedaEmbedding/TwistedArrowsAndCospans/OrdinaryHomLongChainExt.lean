module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedRead

/-!
概要：edgewise の長い射列は左右の制限と中央の隣接射で決まる。
方針：既存の ComposableArrows.ext を左右の区間と中央の三場合で使う。
規約：新しい nerve の模型を定義せず、既存の全射列の等式の検査だけを分割する。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の Hom 模型比較の余単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

private lemma mapIndices_heq (L : ComposableArrows C (n + n + 1))
    {i j i' j' : Fin (n + n + 1 + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (L.map f) (L.map g) := by
  subst i' j'
  have hh : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 長い射列の左右の制限と中央の同じ射の一致から、全射列が一致する。
Kerodon Proposition 8.1.1.10（Tag 03JN）、既存の射列の外延性を三場合に分割した法則。 -/
lemma ordinaryHomLongChain_ext (L M : ComposableArrows C (n + n + 1))
    (hl : (joinLeftOrderHom n n).toFunctor ⋙ L = (joinLeftOrderHom n n).toFunctor ⋙ M)
    (hr : (joinRightOrderHom n n).toFunctor ⋙ L = (joinRightOrderHom n n).toFunctor ⋙ M)
    (hc : HEq (L.map' n (n + 1)) (M.map' n (n + 1))) : L = M := by
  have ho : ∀ k, L.obj k = M.obj k := by
    intro k
    by_cases hk : k.val < n + 1
    · let i : Fin (n + 1) := ⟨k.val, hk⟩
      have he : joinLeftOrderHom n n i = k := by apply Fin.ext; rfl
      have hh := CategoryTheory.Functor.congr_obj hl i
      change L.obj (joinLeftOrderHom n n i) = M.obj (joinLeftOrderHom n n i) at hh
      simpa only [he] using hh
    · let i : Fin (n + 1) := ⟨k.val - (n + 1), by have := k.isLt; omega⟩
      have he : joinRightOrderHom n n i = k := by
        apply Fin.ext
        dsimp [i, joinRightOrderHom]
        omega
      have hh := CategoryTheory.Functor.congr_obj hr i
      change L.obj (joinRightOrderHom n n i) = M.obj (joinRightOrderHom n n i) at hh
      simpa only [he] using hh
  apply ComposableArrows.ext ho
  intro i hi
  apply (conj_eqToHom_iff_heq _ _ (ho _) (ho _)).mpr
  by_cases hil : i < n
  · let a : Fin (n + 1) := ⟨i, by omega⟩
    let b : Fin (n + 1) := ⟨i + 1, by omega⟩
    exact CategoryTheory.Functor.hcongr_hom hl (homOfLE (show a ≤ b by change i ≤ i + 1; omega))
  · by_cases hic : i = n
    · subst i
      exact hc
    · let a : Fin (n + 1) := ⟨i - (n + 1), by omega⟩
      let b : Fin (n + 1) := ⟨i + 1 - (n + 1), by omega⟩
      have ha : joinRightOrderHom n n a = (⟨i, by omega⟩ : Fin (n + n + 1 + 1)) := by
        apply Fin.ext
        dsimp [a, joinRightOrderHom]
        omega
      have hb : joinRightOrderHom n n b = (⟨i + 1, by omega⟩ : Fin (n + n + 1 + 1)) := by
        apply Fin.ext
        dsimp [b, joinRightOrderHom]
        omega
      have hab : a ≤ b := by change i - (n + 1) ≤ i + 1 - (n + 1); omega
      exact (mapIndices_heq L ha.symm hb.symm _ _).trans
        ((CategoryTheory.Functor.hcongr_hom hr (homOfLE hab)).trans
          (mapIndices_heq M ha hb _ _))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
