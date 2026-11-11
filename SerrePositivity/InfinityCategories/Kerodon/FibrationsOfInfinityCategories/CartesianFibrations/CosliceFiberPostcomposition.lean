module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：後合成による終点固定の coslice の比較と三角形の両射影の自然性。
方針：coslice の後合成を頂点 fiber へ制限し、図式の制限との可換性を使う。
規約：後合成する射は任意、同値の判定時には全空間の quasicategory 性を要求する。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、Proposition 5.1.6.7（Tag 01VB）、cocartesian 辺による写像空間比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：後合成する関手は終点固定の錐の空間に射を誘導する。
方針：coslice の後合成と射影の可換性で標的の fiber へ持ち上げる。
規約：固定終点 y は関手の像 f(y) に移す。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、三角形と写像空間の比較射。 -/
def coslicePostcompFiberMap {K E F : SSet.{u}} (e : K ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (e ≫ f)) (f.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e f) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：fiber の後合成の後で全体へ含めると coslice の後合成となる。
方針：fiber への持ち上げの式を読む。
規約：全次数で厳密に可換。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、比較図式の検査。 -/
lemma coslicePostcompFiberMap_ι {K E F : SSet.{u}} (e : K ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    coslicePostcompFiberMap e f y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (e ≫ f)) (f.app (Opposite.op ⦋0⦌) y) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：終点固定の錐における後合成は固定図式の制限と可換。
方針：fiber の包含の後で coslice の制限と後合成の可換性を使う。
規約：二つの図式の合成の括弧は圏の結合則で同定する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、三角形の両射影の比較。 -/
lemma coslicePostcompFiberMap_restrict {K L E F : SSet.{u}}
    (e : K ⟶ E) (i : L ⟶ K) (f : E ⟶ F) (y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e i y ≫ coslicePostcompFiberMap (i ≫ e) f y =
      coslicePostcompFiberMap e f y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (e ≫ f) i (f.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- 概要：cocartesian 辺を保つ比較は終点側の写像空間の同値を始点側へ移す。
方針：三角形の両射影の自明 Kan fibration 性と自然性に、同値の二つから三つ目を得る性質を適用する。
規約：比較関手は共通の標準区間を保ち、固定辺は標準辺を被覆する。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、Proposition 5.1.6.7（Tag 01VB）、前向きの写像空間比較の中心部分。 -/
lemma coslicePostcompFiberMap_source_equivalence_of_target
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (e : (Δ[1] : SSet.{u}) ⟶ E) (hp : e ≫ p = 𝟙 Δ[1])
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hef : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f)))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coslicePostcompFiberMap (stdSimplex.δ (0 : Fin 2) ≫ e) f y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coslicePostcompFiberMap (stdSimplex.δ (1 : Fin 2) ≫ e) f y) := by
  have hpf : (e ≫ f) ≫ q = 𝟙 Δ[1] := by rw [Category.assoc, hf, hp]
  have hyf : q.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) y) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) :=
    (congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) y) hf).trans hy
  have hT0 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration e y
  have hT1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration (e ≫ f) (f.app (Opposite.op ⦋0⦌) y)
  have hS0 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleSource_trivialKanFibration p e hp he y hy
  have hS1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleSource_trivialKanFibration q (e ≫ f) hpf hef
    (f.app (Opposite.op ⦋0⦌) y) hyf
  have hT0e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y)
  have hT1e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (e ≫ f) (stdSimplex.δ (0 : Fin 2)) (f.app (Opposite.op ⦋0⦌) y))
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coslicePostcompFiberMap e f y) := by
    apply hT1e.cancel_right
    rw [← coslicePostcompFiberMap_restrict e (stdSimplex.δ (0 : Fin 2)) f y]
    exact hT0e.comp ht
  have hS0e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) y)
  have hS1e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (e ≫ f) (stdSimplex.δ (1 : Fin 2)) (f.app (Opposite.op ⦋0⦌) y))
  apply hS0e.cancel_left
  rw [coslicePostcompFiberMap_restrict e (stdSimplex.δ (1 : Fin 2)) f y]
  exact hm.comp hS1e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
