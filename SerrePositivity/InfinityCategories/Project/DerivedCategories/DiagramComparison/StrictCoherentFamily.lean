module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexMapPullback

/-!
概要：通常圏を全パラメーターとする、元の coherent 図式の厳密な成分族を記述する。
方針：単体ごとの全 HA 写像に恒等・合成・面・退化との整合性を持たせる。
規約：これは全族の構成に用いるデータ型であり、指定余錐の自然性の結論ではない。
使われ方：3b-3 R6、元の標準脚を持つ余錐を射列と同時に組み立てる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 全 HA 成分の厳密可換式を持つ通常圏上の coherent 図式の族。 -/
structure StrictCoherentFamily (A : Type u) [CommRing A] (E : Type v) [DGCategory A E]
    (I : SSet.{u}) (C : Type w) [Category.{w'} C] where
  /-- 各パラメーターでの元の全 coherent 図式。 -/
  obj : C → ((SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve A E)
  /-- 元の射を、同じ単体の全 HA 成分と可換する写像へ送る。 -/
  map : ∀ {c d : C}, (c ⟶ d) → ∀ {n : ℕ} (s : I _⦋n⦌),
    StrictSimplexMap A E (coherentDiagramSimplex (obj c) s).toSimplexData
      (coherentDiagramSimplex (obj d) s).toSimplexData
  /-- 同じ恒等射の元の成分。 -/
  map_id : ∀ c {n : ℕ} (s : I _⦋n⦌),
    map (𝟙 c) s = StrictSimplexMap.id (coherentDiagramSimplex (obj c) s).toSimplexData
  /-- 同じ合成射の元の成分。 -/
  map_comp : ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e) {n : ℕ} (s : I _⦋n⦌),
    map (f ≫ g) s = (map f s).comp (map g s)
  /-- 全面・退化との整合性。元の二つの表示の間の異種等号で述べる。 -/
  map_pullback : ∀ {c d : C} (f : c ⟶ d) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : I _⦋n⦌),
    HEq (map f (I.map (SimplexCategory.mkHom α).op s)) ((map f s).pullback α)

/-- 有限射列と同じ次元の元の HA 単体を組み合わせるための局所データ。 -/
structure OrderedSimplexFamily (A : Type u) [CommRing A] (E : Type v) [DGCategory A E]
    (n : ℕ) where
  /-- 射列の各位置での元の単体。 -/
  obj : Fin (n + 1) → Simplex A E n
  /-- 昇順の位置の間の全 HA 写像。 -/
  map : ∀ a b, a ≤ b → StrictSimplexMap A E (obj a).toSimplexData (obj b).toSimplexData
  /-- 同じ位置での元の単位。 -/
  map_refl : ∀ a, map a a le_rfl = StrictSimplexMap.id (obj a).toSimplexData
  /-- 三位置での元の合成。 -/
  map_trans : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c),
    (map a b hab).comp (map b c hbc) = map a c (hab.trans hbc)

namespace StrictCoherentFamily
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
  {I : SSet.{u}} {C : Type w} [Category.{w'} C]

/-- パラメーターの有限射列と元の単体から作る、同じ全 HA 射の局所族。 -/
def orderedSimplexFamily (F : StrictCoherentFamily A E I C) {n : ℕ}
    (d : Fin (n + 1) ⥤ C) (s : I _⦋n⦌) : OrderedSimplexFamily A E n where
  obj a := coherentDiagramSimplex (F.obj (d.obj a)) s
  map a b hab := F.map (d.map (homOfLE hab)) s
  map_refl a := by
    simpa only [homOfLE_refl, CategoryTheory.Functor.map_id] using F.map_id (d.obj a) s
  map_trans a b c hab hbc := by
    rw [← F.map_comp, ← d.map_comp]
    rfl

end StrictCoherentFamily
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
