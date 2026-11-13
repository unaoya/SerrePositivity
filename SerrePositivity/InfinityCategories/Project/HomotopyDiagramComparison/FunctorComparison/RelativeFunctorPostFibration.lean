module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration

/-!
概要：left fibration による相対関手空間の後合成は Kan fibration。
方針：同じ底の頂点 fiber への射の持ち上げを構成し、内部 Hom に適用する。
規約：底やパラメーターの充填性は不要。モデル構造の instance 仮定を追加しない。
使われ方：引き戻しの全共変 Hom 図式の一脚 fibration 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：同じ底上の left fibration は頂点 fiber 間でも left fibration。
方針：元の全空間の持ち上げを作り、底への等式で固定 fiber へ戻す。
規約：元の二射影の充填性を要求しない。
使われ方：相対関手の後合成のパラメーター付き持ち上げ。 -/
lemma vertexFiberMap_leftFibration {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f] (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) where
  mem := by
    intro A D j hj
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := f) j hj
    constructor
    intro a c sq
    have s : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) j f (c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) := by
      constructor
      rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι p q f hf b,
        ← Category.assoc, sq.w, Category.assoc]
    let L := s.lift
    have hL : L ≫ p = SSet.const b := by
      rw [← hf, ← Category.assoc, s.fac_right, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
      rfl
    refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b L hL, fac_left := ?_, fac_right := ?_ }
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
      change j ≫ L = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
      exact s.fac_left
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
      change L ≫ f = c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
      exact s.fac_right

/-- 概要：left fibration による相対関手の後合成は left fibration。
方針：内部 Hom の left fibration を固定図式の fiber に制限する。
規約：固定図式 a と元の底を保持する。
使われ方：相対関手の全写像空間の引き戻し。 -/
lemma relativeFunctorPost_leftFibration {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f] (a : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a) :=
  vertexFiberMap_leftFibration ((ihom A).map p) ((ihom A).map q) ((ihom A).map f)
    (by rw [← CategoryTheory.Functor.map_comp, hf]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 概要：left fibrations 間の left fibration による相対関手の後合成は Kan fibration。
方針：相対関手空間の Kan 性と後合成の左ホーン持ち上げを合わせる。
規約：Fibration を結論にし、モデル構造の instance は入力にしない。
使われ方：全余錐比較の cospan の豊穣極限判定。 -/
lemma relativeFunctorPost_fibration {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration f] (a : A ⟶ B) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a) := by
  have := relativeFunctorPost_leftFibration p q f hf a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.leftFibration_fibration_of_kanComplex _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
