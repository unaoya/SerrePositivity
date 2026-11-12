module
public import SerrePositivity.KST.SConstruction.DGComposeDegreeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

/-! # 元の dg 合成と HA 切断合成の異種等号
概要：元の次数・端点・頂点部分集合の等号を保ち、実合成の値を比較する。
方針：元の添字等号を消去し、同じ射と HA 切断合成に戻す。
規約：通常順合成の元の順序を保持。使われ方：実一面像の HA 切断成分評価。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の両因子と出力の次数が一致すれば、異種等号は元の通常順合成へ伝播する。 -/
lemma dgCompose_heq {x y z : D} {p q k p' q' k' : ℤ}
    (hp : p = p') (hq : q = q') (hk : k = k')
    (f : GradedHom A x y p) (g : GradedHom A y z q)
    (f' : GradedHom A x y p') (g' : GradedHom A y z q')
    (h : p + q = k) (h' : p' + q' = k') (hf : HEq f f') (hg : HEq g g') :
    HEq (compose A g f h) (compose A g' f' h') := by
  cases hp
  cases hq
  cases hk
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- 元の頂点集合・両端・次数と切断頂点が一致すれば、同じ HA 切断合成を回収する。 -/
lemma simplexHACutComposite_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {I J : Finset (Fin (n + 1))} {a b a' b' j j' : Fin (n + 1)} {k k' : ℤ}
    {hI : 2 ≤ I.card} {ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)}
    {hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} {hk : k = 2 - (I.card : ℤ)}
    {hj : j ∈ I} {haj : a < j} {hjb : j < b}
    {hJ : 2 ≤ J.card} {ha' : a' = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)}
    {hb' : b' = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)} {hk' : k' = 2 - (J.card : ℤ)}
    {hj' : j' ∈ J} {haj' : a' < j'} {hjb' : j' < b'}
    (hIJ : I = J) (haa : a = a') (hbb : b = b') (hkk : k = k') (hjj : j = j') :
    HEq (s.cutComposite I a b k hI ha hb hk j hj haj hjb)
      (s.cutComposite J a' b' k' hJ ha' hb' hk' j' hj' haj' hjb') := by
  cases hIJ
  cases haa
  cases hbb
  cases hkk
  cases hjj
  rfl

end SerrePositivity.KST.SConstruction
