module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! # 充満 dg 部分圏の dg nerve の像

概要：充満 dg 部分圏の包含の dg nerve の像は、指定対象を全頂点に持つ充満部分単体集合。
方針：対象の性質を各頂点に課す部分複体を作り、射と方程式をそのまま持ち上げる。
規約：HA Construction 1.3.1.6。使われ方：semifree 複体などの充満 dg 部分圏の包含。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 概要：全頂点の対象が性質 P を持つ dg nerve の充満部分単体集合。
方針：各次元で全対象に P を課し、引き戻しは対象の前合成なので閉じる。
規約：HA Construction 1.3.1.6。使われ方：充満 dg 部分圏の dg nerve の像の記述。 -/
def fullOnObjects : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).Subcomplex where
  obj _ := {s | ∀ i, P (s.obj i)}
  map α _ hs i := hs (α.unop.toOrderHom i)

/-- 概要：全対象が P を持つ単体は、充満 dg 部分圏の単体へ持ち上がる。
方針：対象に P の証明を添え、Hom 複体と全ての方程式を元のまま使う。
規約：HA Construction 1.3.1.6。使われ方：充満部分単体集合の像への包含。 -/
def liftToFull {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (hs : ∀ i, P (s.obj i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFullSubcategory D P) n where
  obj i := ⟨s.obj i, hs i⟩
  hom I a b k hI ha hb hk := s.hom I a b k hI ha hb hk
  equation I a b k hI ha hb hk := s.equation I a b k hI ha hb hk

/-- 概要：充満部分圏へ持ち上げた単体の包含による像は元の単体。
方針：対象と Hom 複体上の包含の恒等写像を各成分で評価する。
規約：HA Construction 1.3.1.6。使われ方：包含の像と充満部分単体集合の一致。 -/
lemma map_inclusion_lift {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (hs : ∀ i, P (s.obj i)) :
    (liftToFull A D P s hs).map (dgFullSubcategoryInclusion A D P) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    rfl

/-- 概要：充満 dg 部分圏の包含の dg nerve の像は、その対象で張られる充満部分単体集合。
方針：像の各頂点は P を持ち、逆向きにはその証明で単体を部分圏へ持ち上げる。
規約：HA Construction 1.3.1.6。使われ方：導来 ∞ 圏の充満部分圏としての扱い。 -/
lemma range_inclusion :
    SSet.Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) =
      fullOnObjects A D P := by
  ext n s
  constructor
  · rintro ⟨t, rfl⟩
    exact fun i => (t.obj i).property
  · intro hs
    refine ⟨liftToFull A D P s hs, ?_⟩
    exact map_inclusion_lift A D P s hs

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
