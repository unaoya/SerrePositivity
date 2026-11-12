module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinFaces

/-!
概要：点と nerve の join の同型は元の圏の関手について自然である。
方針：補った nerve の評価と関手による写像を比較し、前半は始対象の一意性を使う。
規約：関手の忠実性や対象上の単射性は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐の境界の可換図式。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：補った nerve の頂点の評価は元の圏の関手と可換である。
方針：空の添字を除き、nerveMap の対象への作用を読む。
規約：関手による写像は空単体にも作用する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の比較の関手に関する自然性。 -/
lemma augNerveObj_augHom (G : C ⥤ D) {r : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) (i : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (nerveMap G) r τ) i = G.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj τ i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

private lemma aug_map_hom (G : C ⥤ D) {r : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) {i j : Fin r} (h : i ≤ j) :
    HEq ((WithInitial.incl : D ⥤ WithInitial D).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (nerveMap G) r τ) h))
      ((WithInitial.map G).map ((WithInitial.incl : C ⥤ WithInitial C).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h))) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

/-- 概要：join から読んだ対象は元の圏の関手の WithInitial への拡張と可換である。
方針：切断の前後で場合分けし、後半は補った nerve の評価の可換性を使う。
規約：新しい始対象を厳密に保つ拡張を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の同型の関手に関する自然性。 -/
lemma initialJoinObj_joinMap (G : C ⥤ D) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i =
      (WithInitial.map G).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj s i) := by
  by_cases hi : i.val < s.1.val
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi).trans
        (congrArg (WithInitial.map G).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star s i hi)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of s i hi]
    change WithInitial.of (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (nerveMap G) _ s.2.2) _) =
      WithInitial.of (G.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2 _))
    rw [augNerveObj_augHom]
    rfl

/-- 概要：join から読んだ射は関手の WithInitial への拡張と端点の移送を介して一致する。
方針：前半は始対象の射の一意性、後半は nerveMap の射への作用を使う。
規約：端点の型の差を HEq で明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の関手に関する自然性。 -/
lemma initialJoinMap_joinMap (G : C ⥤ D) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) h)
      ((WithInitial.map G).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap s h)) := by
  by_cases hi : i.val < s.1.val
  · apply (conj_eqToHom_iff_heq _ _
      (initialJoinObj_joinMap G s i) (initialJoinObj_joinMap G s j)).1
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi
    have : Subsingleton
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) j) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · have hi' : ¬ i.val <
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hi
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap, dite_eq_right hi', dite_eq_right hi, Functor.map_comp,
      eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    exact aug_map_hom G s.2.2 _

/-- 概要：join から構成した射列は関手による写像と可換である。
方針：対象の等式と射の異種等式を関手の外延性で組み合わせる。
規約：関手の忠実性や対象上の単射性を要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の同型の関手に関する自然性。 -/
lemma initialJoinChain_joinMap (G : C ⥤ D) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G)).app (Opposite.op ⦋n⦌) s) =
      ((WithInitial.map G).mapComposableArrows n).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain s) := by
  refine CategoryTheory.Functor.hext (initialJoinObj_joinMap G s) ?_
  intro i j f
  exact initialJoinMap_joinMap G s (leOfHom f)

/-- 概要：点と nerve の join の同型の順方向は元の圏の関手について自然である。
方針：全次数で射列の写像との可換性を使う。
規約：自然性は単体集合の実際の射の等式。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐と標準境界の比較。 -/
@[reassoc]
lemma initialJoinNerveMap_naturality (G : C ⥤ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap C ≫ nerveMap (WithInitial.map G) := by
  ext n s
  exact initialJoinChain_joinMap G s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
