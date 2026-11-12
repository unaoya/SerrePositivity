module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NervePrefixes
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合値の通常の関手の weighted nerve と、その底の nerve への射影。
方針：底の合成可能射列と、初区間の標準単体からの自然変換の組を各単体とする。
規約：τ_i は F(C_i) の i 単体であり、各底の射と初区間の包含に関して可換。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、strict transport の表現からの全空間の復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：単調写像は初区間の重みの制限の自然変換を与える。
方針：各添字 i で α の初区間への制限の標準単体の射を取る。
規約：標的の重みは α の順序関手で引き戻す。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の各単体の制限。 -/
def simplexPrefixWeightRestriction {m n : SimplexCategory} (α : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight.{u} m.len ⟶
      (SimplexCategory.toCat.map α).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n.len where
  app i := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i)
  naturality i j f := by
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α j) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i) ≫
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.toOrderHom i).val
          (α.toOrderHom j).val (α.toOrderHom.monotone (leOfHom f)))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_naturality]

/-- 概要：weighted nerve の n 単体の型。
方針：底の n 個の合成可能射と、その射列上の初区間の重みからの自然変換を組にする。
規約：F の Kan 性は単体の定義には要求しない。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の次数ごとのデータ。 -/
def weightedNerveSimplex {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (n : ℕ) : Type u :=
  Σ σ : ComposableArrows C n, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ F)

/-- 概要：weighted nerve の単体を単調写像で制限する。
方針：底の射列を引き戻し、τ の族を重みの制限の自然変換で前合成する。
規約：α:m→n は n 単体を m 単体へ写す。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の面と退化の作用。 -/
def weightedNerveSimplexMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (s : weightedNerveSimplex F n.len) :
    weightedNerveSimplex F m.len :=
  ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ s.1,
    simplexPrefixWeightRestriction α ≫
      CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor s.2⟩

/-- 概要：単体集合値関手 F の weighted nerve。
方針：合成可能射列と初区間の図式の組を取り、重みの制限で単体作用素を定める。
規約：通常の nerve 上に射影する単体集合として構成し、充填性は後で示す。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、strict diagram から fibration への構成。 -/
@[kerodon 025X]
def weightedNerve {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) : SSet.{u} where
  obj d := weightedNerveSimplex F d.unop.len
  map α := ↾weightedNerveSimplexMap F α.unop
  map_id d := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    change weightedNerveSimplexMap F (𝟙 d.unop) ⟨σ, τ⟩ = ⟨σ, τ⟩
    dsimp only [weightedNerveSimplexMap]
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction (𝟙 d.unop) i) ≫ τ.app i = τ.app i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_id, CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    change weightedNerveSimplexMap F (β.unop ≫ α.unop) ⟨σ, τ⟩ =
      weightedNerveSimplexMap F β.unop (weightedNerveSimplexMap F α.unop ⟨σ, τ⟩)
    dsimp only [weightedNerveSimplexMap]
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction (β.unop ≫ α.unop) i) ≫
        τ.app ((β.unop ≫ α.unop).toOrderHom i) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β.unop i) ≫
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop (β.unop.toOrderHom i)) ≫
          τ.app (α.unop.toOrderHom (β.unop.toOrderHom i)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_comp, CategoryTheory.Functor.map_comp, Category.assoc]
    rfl

/-- 概要：weighted nerve から底の通常の nerve への射影。
方針：各単体の対から合成可能射列を取り出す。
規約：τ の重み付き図式だけを忘れる。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、Kan 値関手から構成する fibration の射影。 -/
@[kerodon 025X]
def weightedNerveProjection {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    weightedNerve F ⟶ nerve C where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
