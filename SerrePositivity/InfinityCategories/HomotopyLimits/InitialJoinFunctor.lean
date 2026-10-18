module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinFaces

/-!
概要：点と nerve の join の同型は元の圏の関手について自然である。
方針：補った nerve の評価と関手による写像を比較し、前半は始対象の一意性を使う。
規約：関手の忠実性や対象上の単射性は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の相対錐の境界の可換図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：補った nerve の頂点の評価は元の圏の関手と可換である。
方針：空の添字を除き、nerveMap の対象への作用を読む。
規約：関手による写像は空単体にも作用する。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の join の比較の関手に関する自然性。 -/
lemma augNerveObj_augHom (G : C ⥤ D) {r : ℕ}
    (τ : Join.augObj (nerve C) r) (i : Fin r) :
    augNerveObj (Join.augHom (nerveMap G) r τ) i = G.obj (augNerveObj τ i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

private lemma aug_map_hom (G : C ⥤ D) {r : ℕ}
    (τ : Join.augObj (nerve C) r) {i j : Fin r} (h : i ≤ j) :
    HEq ((WithInitial.incl : D ⥤ WithInitial D).map
      (augNerveMap (Join.augHom (nerveMap G) r τ) h))
      ((WithInitial.map G).map ((WithInitial.incl : C ⥤ WithInitial C).map
        (augNerveMap τ h))) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

/-- 概要：join から読んだ対象は元の圏の関手の WithInitial への拡張と可換である。
方針：切断の前後で場合分けし、後半は補った nerve の評価の可換性を使う。
規約：新しい始対象を厳密に保つ拡張を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の同型の関手に関する自然性。 -/
lemma initialJoinObj_joinMap (G : C ⥤ D) {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (n + 1)) :
    initialJoinObj ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i =
      (WithInitial.map G).obj (initialJoinObj s i) := by
  by_cases hi : i.val < s.1.val
  · exact (initialJoinObj_star
      ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi).trans
        (congrArg (WithInitial.map G).obj (initialJoinObj_star s i hi)).symm
  · rw [initialJoinObj_of
      ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi,
      initialJoinObj_of s i hi]
    change WithInitial.of (augNerveObj (Join.augHom (nerveMap G) _ s.2.2) _) =
      WithInitial.of (G.obj (augNerveObj s.2.2 _))
    rw [augNerveObj_augHom]
    rfl

/-- 概要：join から読んだ射は関手の WithInitial への拡張と端点の移送を介して一致する。
方針：前半は始対象の射の一意性、後半は nerveMap の射への作用を使う。
規約：端点の型の差を HEq で明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の比較射の関手に関する自然性。 -/
lemma initialJoinMap_joinMap (G : C ⥤ D) {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    HEq (initialJoinMap ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) h)
      ((WithInitial.map G).map (initialJoinMap s h)) := by
  by_cases hi : i.val < s.1.val
  · apply (conj_eqToHom_iff_heq _ _
      (initialJoinObj_joinMap G s i) (initialJoinObj_joinMap G s j)).1
    have he := initialJoinObj_star
      ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi
    have : Subsingleton
        (initialJoinObj ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i ⟶
          initialJoinObj
            ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) j) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · have hi' : ¬ i.val <
        ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hi
    simp only [initialJoinMap, dite_eq_right hi', dite_eq_right hi, Functor.map_comp,
      eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    exact aug_map_hom G s.2.2 _

/-- 概要：join から構成した射列は関手による写像と可換である。
方針：対象の等式と射の異種等式を関手の外延性で組み合わせる。
規約：関手の忠実性や対象上の単射性を要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の同型の関手に関する自然性。 -/
lemma initialJoinChain_joinMap (G : C ⥤ D) {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    initialJoinChain ((joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) =
      ((WithInitial.map G).mapComposableArrows n).obj (initialJoinChain s) := by
  refine CategoryTheory.Functor.hext (initialJoinObj_joinMap G s) ?_
  intro i j f
  exact initialJoinMap_joinMap G s (leOfHom f)

/-- 概要：点と nerve の join の同型の順方向は元の圏の関手について自然である。
方針：全次数で射列の写像との可換性を使う。
規約：自然性は単体集合の実際の射の等式。
使われ方：HTT 1.2.8、Kerodon 4.3.5 の相対錐と標準境界の比較。 -/
@[reassoc]
lemma initialJoinNerveMap_naturality (G : C ⥤ D) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G) ≫ initialJoinNerveMap D =
      initialJoinNerveMap C ≫ nerveMap (WithInitial.map G) := by
  ext n s
  exact initialJoinChain_joinMap G s

end SerrePositivity.InfinityCategories.HomotopyLimits
