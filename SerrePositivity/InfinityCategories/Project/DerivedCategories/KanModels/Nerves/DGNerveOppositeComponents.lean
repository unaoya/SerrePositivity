module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanSuffixReplacementTransport
/-!
概要：符号付き頂点反転と、HA 微分式の削除成分・左右切断との照合。
方針：反転した実添字の等式を全成分の異種等号へ送る。
規約：元の全 Hom と実端点を保持。使われ方：反対模型の微分方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {n : ℕ}
variable (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
  (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
/-- 内部点を消した実成分の反転は、同じ消去後濃度の符号倍。 -/
lemma op_erasedComponent :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).erasedComponent I a b k hI ha hb hk j hj haj hjb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.erase j).card •
        s.erasedComponent (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) j.rev
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj)
          (Fin.rev_lt_rev.mpr hjb) (Fin.rev_lt_rev.mpr haj) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.erasedComponent, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op]
  apply congrArg (fun x ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.erase j).card • x)
  exact eq_of_heq (s.hom_heq_of_indices_degree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_erase I j) rfl rfl rfl)
/-- 左切断の反転は、同じ実右切断の符号倍。次数の輸送も保持する。 -/
lemma op_cutLeft :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).cutLeft I a hI ha j hj haj)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (· ≤ j)).card •
        s.cutRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) a.rev (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha) j.rev
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj) (Fin.rev_lt_rev.mpr haj)) := by
  have hc : (I.filter (· ≤ j)).card = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev ≤ ·)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.cutLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.cutRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq rfl rfl (by omega)
  exact s.hom_heq_of_indices_degree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_left I j) rfl rfl (by omega)
/-- 右切断の反転は、同じ実左切断の符号倍。次数の輸送も保持する。 -/
lemma op_cutRight :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).cutRight I b hI hb j hj hjb)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (j ≤ ·)).card •
        s.cutLeft (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) j.rev
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj) (Fin.rev_lt_rev.mpr hjb)) := by
  have hc : (I.filter (j ≤ ·)).card = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (· ≤ j.rev)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.cutLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.cutRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq rfl rfl (by omega)
  exact s.hom_heq_of_indices_degree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_right I j) rfl rfl (by omega)
/-- 反転した実切断合成は、逆順合成と dg 反対圏の実 Koszul 符号で与えられる。 -/
lemma op_cutComposite :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).cutComposite I a b k hI ha hb hk j hj haj hjb =
      (((2 - ((I.filter (· ≤ j)).card : ℤ)) *
        (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow *
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (· ≤ j)).card *
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (I.filter (j ≤ ·)).card) •
        s.cutComposite (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) j.rev
          (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj)
          (Fin.rev_lt_rev.mpr hjb) (Fin.rev_lt_rev.mpr haj) := by
  have hL : (I.filter (· ≤ j)).card = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev ≤ ·)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse]
  have hR : (I.filter (j ≤ ·)).card = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (· ≤ j.rev)).card := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse]
  have hf := op_cutLeft s I a hI ha j hj haj
  have hg := op_cutRight s I b hI hb j hj hjb
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.cutComposite]
  rw [_root_.SerrePositivity.DifferentialGraded.opposite_compose]
  rw [mul_smul, mul_smul]
  apply congrArg (fun z ↦
    ((2 - ((I.filter (· ≤ j)).card : ℤ)) *
      (2 - ((I.filter (j ≤ ·)).card : ℤ))).negOnePow • z)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := D)
    (x := s.obj b.rev) (y := s.obj j.rev) (z := s.obj a.rev)
    (k := k + 1) (k' := k + 1) rfl rfl rfl
    (show 2 - ((I.filter (j ≤ ·)).card : ℤ) =
      2 - (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (· ≤ j.rev)).card : ℤ) by rw [hR])
    (show 2 - ((I.filter (· ≤ j)).card : ℤ) =
      2 - (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).filter (j.rev ≤ ·)).card : ℤ) by rw [hL]) rfl
    _ _ _ _ hf hg
    (by have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega)
    (by have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card
          (show j.rev ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hj)
        have hcard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse I
        omega)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, smul_smul, mul_comm]
    using eq_of_heq he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
