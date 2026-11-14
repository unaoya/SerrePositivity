module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorInverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorFiberHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison

/-!
概要：同じ quasicategory 上の left fibrations の全空間の同値は各 fiber の同値を誘導する。
方針：底上の相対逆と単位・余単位を、相対 Hom の fiber への作用で制限する。
規約：fiber ごとの十分条件と合わせて、両方向の同値判定を得る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の全空間の同値から transport の比較を使う。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：left fibrations の底上の前合成同値は各 fiber に同値を誘導する。
方針：相対逆を fiber へ制限し、相対的な単位・余単位を fiber 内の関手同型へ写す。
規約：底 B は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、選択された全空間比較から fiber の同値性を回収する。 -/
lemma vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  obtain ⟨g, hg, ⟨hunit⟩, ⟨hcounit⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence p q f hf ef
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hunit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom p p b)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom_vertex p p b (f ≫ g) (by rw [Category.assoc, hg, hf]),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom_vertex p p b (𝟙 E) (Category.id_comp p)] at hu
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hcounit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom q q b)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom_vertex q q b (g ≫ f) (by rw [Category.assoc, hf, hg]),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorFiberHom_vertex q q b (𝟙 F) (Category.id_comp q)] at hc
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p g hg b, ⟨?_⟩, ⟨?_⟩⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp p q p f g hf hg b]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id] using hu
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp q p q g f hg hf b]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id] using hc

/-- 概要：quasicategory 上の left fibrations の底上の射の前合成同値性は、全 fiber の同値性と一致する。
方針：相対逆による必要条件と、標準単体上の比較による十分条件を組み合わせる。
規約：fiber 側の条件はすべての底の頂点で要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の全空間と値の双方の比較を往復する。 -/
lemma leftFibration_precompositionEquivalence_iff_fibers
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f ↔
      ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) :=
  ⟨fun ef b ↦ vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q f hf ef b,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPrecompositionEquivalence_of_leftFibration_fibers p q f hf⟩

/-- 概要：quasicategory 上の left fibrations の底上の射は、全空間で同値であることと全 fiber で同値であることが同値。
方針：前合成同値性との同値と fiber 判定を使う。
規約：全空間の quasicategory 性は底の quasicategory 性と射影の left fibration 性からも得られる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の比較射の fiber ごとの同値性。 -/
lemma leftFibration_isQCatEquivalence_iff_fibers
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f ↔ ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  constructor
  · intro ef
    exact (leftFibration_precompositionEquivalence_iff_fibers p q f hf).mp
      ef.isPrecompositionEquivalence
  · intro ef
    exact ((leftFibration_precompositionEquivalence_iff_fibers p q f hf).mpr ef).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.1.3.8" (partial := special) "仮定：準圏 O 上の写像 C→D と射影（Lean が強い：色の上の二つの射影に left fibration を要求）。結論：台の写像が準圏同値であることと各色のファイバーの写像が準圏同値であることの同値（この仮定の下で (2) と (3) に一致）。O-モノイダル関手の全空間の同値 (1) は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers
attribute [cite HTT "4.1.1.7" (partial := special) "仮定：準圏の図式を共終写像で制限する（Lean が強い：元の添字単体集合も準圏）。結論：同じ余錐制限の全空間での同値を、射影との可換性と左ファイブレーションの繊維判定に代入し、各頂点の繊維上の同値を得る（HTT の同じ繊維射。任意の添字単体集合は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_isQCatEquivalence_iff_fibers
