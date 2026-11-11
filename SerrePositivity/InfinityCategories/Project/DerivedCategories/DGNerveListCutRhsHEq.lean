module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutLeibniz
/-!
概要：切断列の添字・次数の一致から元の再帰的 HA 右辺の異種等号を得る。
方針：先頭切断の実 cochain 比較と零拡張した有限和、切断集合への強帰納法を使う。
規約：全次元の同じ実成分を保つ。使われ方：tensor 候補の全 HA の有限和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実切断合成の境界項と符号付き全和の照合。 -/
lemma dgNerveListCutRhs_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    {I J : Finset (Fin (n + 1))} {a b c d : Fin (n + 1)} {L M : List (Fin (n + 1))}
    {k l : ℤ} {hk : k = 2 - (I.card : ℤ) + (L.length : ℤ)}
    {hl : l = 2 - (J.card : ℤ) + (M.length : ℤ)}
    {hI : 2 ≤ I.card} {hJ : 2 ≤ J.card}
    {ha : IsLeast (I : Set (Fin (n + 1))) a} {hb : IsGreatest (I : Set (Fin (n + 1))) b}
    {hc : IsLeast (J : Set (Fin (n + 1))) c} {hd : IsGreatest (J : Set (Fin (n + 1))) d}
    {ho : L.Pairwise (· < ·)} {ho' : M.Pairwise (· < ·)}
    {hL : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b} {hM : ∀ j ∈ M, j ∈ J ∧ c < j ∧ j < d}
    (hIJ : I = J) (hac : a = c) (hbd : b = d) (hLM : L = M) (hkl : k = l) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs R D s I a b L k hk hI ha hb ho hL)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutRhs R D s J c d M l hl hJ hc hd ho' hM) := by
  subst J
  subst c
  subst d
  subst M
  subst l
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
