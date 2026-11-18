module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomLiftedChains
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveJoinBoundaries
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
概要：Hom の元の圏の同じ射列を twisted arrow の単体へ送る。
方針：既存の標準単体・反対 nerve・join の比較を合成し、全再添字を比較する。
規約：頂点だけの同値に置き換えず、指定した交差射を含む全射列を使う。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の全 Hom 図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {m n : ℕ}

/-- edgewise の左因子から反対の添字圏の nerve への指定した模型比較。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ反対添字の読み方。 -/
def homChainLeftWeight (n : ℕ) :
    (stdSimplex.obj ⦋n⦌).op ⟶ nerve (ULift.{u} (Fin (n + 1)))ᵒᵖ :=
  SSet.opFunctor.map (stdSimplex.isoNerve.{u} n).hom ≫ nerveOppositeMap

/-- 左因子の模型比較は全順序写像に自然。
Kerodon Proposition 8.1.1.10（Tag 03JN）、反対添字の模型移送の法則。 -/
lemma homChainLeftWeight_naturality (α : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.opFunctor.map (stdSimplex.map α) ≫ homChainLeftWeight.{u} n =
      homChainLeftWeight.{u} m ≫ nerveMap (homChainIndexMap.{u} α.toOrderHom).op := by
  unfold homChainLeftWeight
  rw [← Category.assoc, ← SSet.opFunctor.map_comp, homChainIndexNerve_naturality,
    SSet.opFunctor.map_comp, Category.assoc, nerveOppositeMap_naturality, Category.assoc]

/-- edgewise の始域を同じ持ち上げた通常圏の join の nerve へ写す。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ全射列の模型比較。 -/
def homChainJoinWeight (n : ℕ) : edgewiseWeight.{u}.obj ⦋n⦌ ⟶
    nerve (CategoryTheory.Join (ULift.{u} (Fin (n + 1)))ᵒᵖ (ULift.{u} (Fin (n + 1)))) :=
  joinMap (homChainLeftWeight n) (stdSimplex.isoNerve.{u} n).hom ≫
    nerveJoinComparison _ _

/-- edgewise の始域の模型比較は左右の全順序写像に自然。
Kerodon Proposition 8.1.1.10（Tag 03JN）、join の模型移送の法則。 -/
lemma homChainJoinWeight_naturality (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.map α ≫ homChainJoinWeight.{u} n =
      homChainJoinWeight.{u} m ≫ nerveMap
        (CategoryTheory.Join.mapPair (homChainIndexMap.{u} α.toOrderHom).op
          (homChainIndexMap.{u} α.toOrderHom)) := by
  unfold homChainJoinWeight
  change joinMap (SSet.opFunctor.map (stdSimplex.map α)) (stdSimplex.map α) ≫
      (joinMap _ _ ≫ _) = _
  rw [← Category.assoc, ← joinMap_comp, homChainLeftWeight_naturality,
    homChainIndexNerve_naturality, joinMap_comp, Category.assoc,
    nerveJoinComparison_naturality, Category.assoc]

/-- Hom の元の圏の射列を、元の交差射を保持した twisted arrow の単体にする。
Kerodon Proposition 8.1.1.10（Tag 03JN）、比較射の各次数の指定写像。 -/
def ordinaryHomTwistedSimplex (s : ComposableArrows (OrdinaryHomElements C) n) :
    edgewiseWeight.{u}.obj ⦋n⦌ ⟶ nerve C :=
  homChainJoinWeight n ≫ nerveMap (ordinaryHomLiftedJoinChain s)

/-- twisted arrow の指定単体は面と退化を含む全再添字と可換。
Kerodon Proposition 8.1.1.10（Tag 03JN）、比較射の全単体的自然性。 -/
lemma ordinaryHomTwistedSimplex_naturality
    (s : ComposableArrows (OrdinaryHomElements C) n) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.map α ≫ ordinaryHomTwistedSimplex s =
      ordinaryHomTwistedSimplex (α.toOrderHom.toFunctor ⋙ s) := by
  unfold ordinaryHomTwistedSimplex
  rw [← Category.assoc, homChainJoinWeight_naturality, Category.assoc]
  have hn :
      nerveMap (CategoryTheory.Join.mapPair (homChainIndexMap.{u} α.toOrderHom).op
        (homChainIndexMap.{u} α.toOrderHom)) ≫ nerveMap (ordinaryHomLiftedJoinChain s) =
      nerveMap (CategoryTheory.Join.mapPair (homChainIndexMap.{u} α.toOrderHom).op
        (homChainIndexMap.{u} α.toOrderHom) ⋙ ordinaryHomLiftedJoinChain s) := rfl
  rw [hn, ordinaryHomLiftedJoinChain_reindex]

/-- 通常の Hom の元の圏の nerve から、指定した twisted arrow への全単体的比較射。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ両端と交差射を持つ模型の比較。 -/
def ordinaryHomTwistedComparison (C : Type u) [SmallCategory C] :
    nerve (OrdinaryHomElements C) ⟶ TwistedArrow (nerve C) where
  app _ := ↾ordinaryHomTwistedSimplex
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (ordinaryHomTwistedSimplex_naturality s α.unop).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
