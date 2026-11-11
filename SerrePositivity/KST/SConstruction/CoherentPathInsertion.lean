module
public import SerrePositivity.KST.SConstruction.CoherentSimplexCompositionEdge
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.OrdinaryComparisonPrism

/-! # Coherent な Path の族への切断点の挿入
概要：全 Path の族を切断点を通る族へ動かし、既に通る部分を全時刻で固定する。
方針：切断点との和集合による関手と元の包含自然変換の nerve を取る。
規約：元の Path の包含方向を保ち、充填やホモトピー代表の選択をしない。
使われ方：元の K prism の高次単体を、境界を保つ豊穣 Hom の合成円柱へ復号する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c : J}

/-- 元の Path に切断点を一つ加える。端点への退化も許す。 -/
def coherentPathInsert (hab : a ≤ b) (hbc : b ≤ c) (p : Path a c) : Path a c where
  I := p.I ∪ {b}
  left := Or.inl p.left
  right := Or.inl p.right
  left_le x hx := by
    rcases hx with hx | rfl
    · exact p.left_le x hx
    · exact hab
  le_right x hx := by
    rcases hx with hx | rfl
    · exact p.le_right x hx
    · exact hbc

/-- 切断点の挿入は全 Path の包含と可換な関手。 -/
def coherentPathInsertFunctor (hab : a ≤ b) (hbc : b ≤ c) : Path a c ⥤ Path a c where
  obj := coherentPathInsert hab hbc
  map f := ⟨⟨⟨fun _ hx => hx.elim (fun h => Or.inl (f.1.1.1 h)) Or.inr⟩⟩⟩

/-- 元の Path から切断点を加えた Path への指定包含。 -/
def coherentPathInsertTransformation (hab : a ≤ b) (hbc : b ≤ c) :
    𝟭 (Path a c) ⟶ coherentPathInsertFunctor hab hbc where
  app _ := ⟨⟨⟨fun _ hx => Or.inl hx⟩⟩⟩

/-- 既に切断点を通る Path は挿入で変わらない。 -/
lemma coherentPathInsert_eq (hab : a ≤ b) (hbc : b ≤ c) (p : Path a c) (hp : b ∈ p.I) :
    coherentPathInsert hab hbc p = p := by
  apply SimplicialThickening.Path.ext
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hp)

/-- 元の全 Path の族から切断点を通る族への実円柱。 -/
def coherentPathInsertionHomotopy (hab : a ≤ b) (hbc : b ≤ c) :
    SSet.Homotopy (𝟙 (nerve (Path a c))) (nerveMap (coherentPathInsertFunctor hab hbc)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy (coherentPathInsertTransformation hab hbc)

/-- 挿入後の全 Path は指定切断点を通る。 -/
def coherentPathInsertThrough (hab : a ≤ b) (hbc : b ≤ c) :
    nerve (Path a c) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b : SSet.{u}) where
  app _ := ↾fun F => ⟨(nerveMap (coherentPathInsertFunctor hab hbc)).app _ F,
    fun _ => Or.inr rfl⟩

/-- 切断点を通る族への因子分解は元の挿入関手の nerve そのもの。 -/
lemma coherentPathInsertThrough_ι (hab : a ≤ b) (hbc : b ≤ c) :
    coherentPathInsertThrough hab hbc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).ι =
      nerveMap (coherentPathInsertFunctor hab hbc) := rfl

/-- 切断点を通る全高次単体は挿入円柱の全時刻で固定する。 -/
lemma coherentPathInsertionHomotopy_relative (hab : a ≤ b) (hbc : b ≤ c) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentPathInsertionHomotopy hab hbc).h =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b : SSet.{u}) Δ[1] ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).ι := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply CategoryTheory.Functor.ext (fun k => ?_)
  change ((ComposableArrows.mk₁ (coherentPathInsertTransformation hab hbc)).obj
    (z.2.down.toOrderHom k)).obj (z.1.val.obj k) = z.1.val.obj k
  generalize z.2.down.toOrderHom k = t
  fin_cases t
  · rfl
  · exact coherentPathInsert_eq hab hbc _ (z.1.property k)

/-- 切断点の挿入は、端点が潰れる順序写像を含む全再添字と厳密に可換。 -/
lemma coherentPathInsert_map {K : Type u} [LinearOrder K] (θ : J →o K)
    (hab : a ≤ b) (hbc : b ≤ c) (p : Path a c) :
    (SimplicialThickening.functorMap θ (.mk a) (.mk c)).obj
        (coherentPathInsert hab hbc p) =
      coherentPathInsert (θ.monotone hab) (θ.monotone hbc)
        ((SimplicialThickening.functorMap θ (.mk a) (.mk c)).obj p) := by
  apply SimplicialThickening.Path.ext
  change θ '' (p.I ∪ {b}) = θ '' p.I ∪ {θ b}
  rw [Set.image_union, Set.image_singleton]

/-- 挿入円柱の全時刻が全順序写像による再添字と厳密に可換。 -/
lemma coherentPathInsertionHomotopy_naturality {K : Type u} [LinearOrder K] (θ : J →o K)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (nerveMap (SimplicialThickening.functorMap θ (.mk a) (.mk c)) ▷
        (Δ[1] : SSet.{u})) ≫
      (coherentPathInsertionHomotopy (θ.monotone hab) (θ.monotone hbc)).h =
    (coherentPathInsertionHomotopy hab hbc).h ≫
      nerveMap (SimplicialThickening.functorMap θ (.mk a) (.mk c)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply CategoryTheory.Functor.ext (fun k => ?_)
  change ((ComposableArrows.mk₁ (coherentPathInsertTransformation
      (θ.monotone hab) (θ.monotone hbc))).obj (z.2.down.toOrderHom k)).obj
      ((SimplicialThickening.functorMap θ (.mk a) (.mk c)).obj (z.1.obj k)) =
    (SimplicialThickening.functorMap θ (.mk a) (.mk c)).obj
      (((ComposableArrows.mk₁ (coherentPathInsertTransformation hab hbc)).obj
        (z.2.down.toOrderHom k)).obj (z.1.obj k))
  generalize z.2.down.toOrderHom k = t
  fin_cases t
  · rfl
  · exact (coherentPathInsert_map θ hab hbc _).symm

/-- 元の端点だけの Path に切断点を挿入すると、元の二端点 Path の合成。 -/
lemma coherentPathInsert_endpoint (hab : a ≤ b) (hbc : b ≤ c) :
    coherentPathInsert hab hbc (coherentEndpointPath (hab.trans hbc)) =
      coherentEndpointPathComposite hab hbc := by
  apply SimplicialThickening.Path.ext
  ext x
  change ((x = a ∨ x = c) ∨ x = b) ↔ ((x = a ∨ x = b) ∨ (x = b ∨ x = c))
  tauto

/-- 端点だけの Path 上で挿入円柱は、以前復号した同じ合成三角形の元の辺。 -/
lemma coherentPathInsertionHomotopy_endpoint_edge (hab : a ≤ b) (hbc : b ≤ c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentPathInsertionHomotopy hab hbc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath (hab.trans hbc)))).edge =
    (nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).edge := by
  rw [show coherentPathInsertionHomotopy hab hbc =
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy (coherentPathInsertTransformation hab hbc) from rfl,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy_vertex]
  refine ComposableArrows.ext₁ rfl (coherentPathInsert_endpoint hab hbc) ?_
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
