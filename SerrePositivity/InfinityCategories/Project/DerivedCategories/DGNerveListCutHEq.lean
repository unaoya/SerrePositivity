module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveListCutProduct
/-!
概要：端点・切断列・指定次数の等式は、同じ実切断合成 cochain の異種等号を与える。
方針：全ての添字の等式を消去し、証明引数の一意性を使う。
規約：実 cochain の比較であり、新たな選択を行わない。使われ方：全次元の制限と微分の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ添字・切断列・次数の実切断合成は、証明引数によらず異種等号で一致する。 -/
lemma dgNerveListCutProduct_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    {I J : Finset (Fin (n + 1))} {a b c d : Fin (n + 1)} {L M : List (Fin (n + 1))}
    {k l : ℤ} {hk : k = 2 - (I.card : ℤ) + (L.length : ℤ)}
    {hl : l = 2 - (J.card : ℤ) + (M.length : ℤ)}
    {hI : 2 ≤ I.card} {hJ : 2 ≤ J.card}
    {ha : IsLeast (I : Set (Fin (n + 1))) a} {hb : IsGreatest (I : Set (Fin (n + 1))) b}
    {hc : IsLeast (J : Set (Fin (n + 1))) c} {hd : IsGreatest (J : Set (Fin (n + 1))) d}
    {ho : L.Pairwise (· < ·)} {ho' : M.Pairwise (· < ·)}
    {hL : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b} {hM : ∀ j ∈ M, j ∈ J ∧ c < j ∧ j < d}
    (hIJ : I = J) (hac : a = c) (hbd : b = d) (hLM : L = M) (hkl : k = l) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s I a b L k hk hI ha hb ho hL)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s J c d M l hl hJ hc hd ho' hM) := by
  subst J
  subst c
  subst d
  subst M
  subst l
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
