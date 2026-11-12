module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeFunctorConstFiberIso

/-!
概要：定値 fiber の相対関手同型を全パラメータで評価する。
方針：点図式の等式による表示変更を消去し、fiber の持ち上げの評価を使う。
規約：充填性を要求せず、実際の射の等式を示す。
使われ方：定値 unstraightening の相対合成を fiber の座標で計算する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：底の図式の等式による相対関手の表示変更は評価を変えない。
方針：等式を消去して恒等合成を簡約する。
規約：全パラメータ。使われ方：定値図式の合成の表示変更の消去。 -/
lemma relativeFunctorUncurry_transport {A T E B : SSet.{u}}
    (p : E ⟶ B) {a b : A ⟶ B} (h : a = b) (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) h)).hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry k := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- 概要：定値底の相対関手同型を評価し包含すると元の相対評価そのもの。
方針：内部 Hom の自然性と fiber の持ち上げの包含の式を使う。
規約：任意の全パラメータ。使われ方：fiber の座標での合成の計算。 -/
lemma relativeConstFiberIso_uncurry {A T E B : SSet.{u}}
    (p : E ⟶ B) (b : B.obj (Opposite.op ⦋0⦌))
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (SSet.const b : A ⟶ B)) :
    uncurry (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeFunctorConstFiberIso p b).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry k := by
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeFunctorConstFiberIso_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom,
    uncurry_curry, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (SSet.const b))) k
  rw [Category.comp_id] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
