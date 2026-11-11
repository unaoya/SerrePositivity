module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：底を保つ全空間の射が誘導する相対関手空間の後合成。
方針：内部 Hom の後合成を、同じ底の関手の頂点 fiber に制限する。
規約：底への二つの射影の可換性を厳密な等式で指定する。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.5.4.6（Tag 03BB） の coherent な錐の二つの模型の自然な比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {A D E E' B : SSet.{u}}

/-- 概要：底を保つ全空間の射による相対関手空間の後合成。
方針：内部 Hom の射を固定した底の頂点の fiber に持ち上げる。
規約：射影自身の充填性は要求しない。
使われ方：Kerodon 5.3.1.5（Tag 035J） の strict transport の全空間に関する関手性。 -/
def relativeFunctorPost (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (a : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((ihom A).map p) ((ihom A).map q) ((ihom A).map f)
    (by rw [← Functor.map_comp, hf]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 概要：相対関手の後合成を内部 Hom に含めると通常の後合成になる。
方針：頂点 fiber の誘導射の包含の計算則を使う。
規約：底の関手 a は変えない。
使われ方：Kerodon 5.3.1.5（Tag 035J） の自然性の検証。 -/
lemma relativeFunctorPost_ι (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (a : A ⟶ B) :
    relativeFunctorPost p q f hf a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (ihom A).map f := rfl

/-- 概要：相対関手の後合成は定義域の前合成と可換である。
方針：fiber の包含後に内部 Hom の前合成の自然性を使う。
規約：定義域の射 r に単射性は要求しない。
使われ方：Kerodon 5.3.1.5（Tag 035J） の under 圏の制限と全空間の比較の可換性。 -/
lemma relativeFunctorPost_pre (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E')
    (hf : f ≫ q = p) (a : A ⟶ B) (r : D ⟶ A) :
    relativeFunctorPost p q f hf a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre q a r =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a r ≫ relativeFunctorPost p q f hf (r ≫ a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom D).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (r ≫ a))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (ihom A).map f) ≫
      (pre r).app E' =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre r).app E) ≫ (ihom D).map f
  rw [Category.assoc, Category.assoc, (pre r).naturality f]

/-- 概要：相対関手の後合成と頂点での評価は可換である。
方針：fiber の包含後に内部 Hom の評価と後合成の可換性を使う。
規約：評価点は定義域 A の任意の頂点。
使われ方：Kerodon 5.3.1.5（Tag 035J） の transport の比較と元の fiber 比較の対応。 -/
lemma relativeFunctorPost_evaluate (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E')
    (hf : f ≫ q = p) (a : A ⟶ B) (v : A.obj (Opposite.op ⦋0⦌)) :
    relativeFunctorPost p q f hf a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate q a v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a v ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (a.app (Opposite.op ⦋0⦌) v) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (a.app (Opposite.op ⦋0⦌) v)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (ihom A).map f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) ≫ f
  rw [Category.assoc, Category.assoc]
  rfl

/-- 概要：相対関手の後合成を展開すると全空間への族の後合成になる。
方針：fiber の包含の式と uncurry の後合成自然性を使う。
規約：パラメータ T は任意。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.5.4.6（Tag 03BB） の切断の制限と全空間の比較の可換性。 -/
lemma relativeFunctorUncurry_post {T : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (f : E ⟶ E') (hf : f ≫ q = p) (a : A ⟶ B) (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (g ≫ relativeFunctorPost p q f hf a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry g ≫ f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
  rw [Category.assoc, relativeFunctorPost_ι, ← Category.assoc, uncurry_natural_right]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
