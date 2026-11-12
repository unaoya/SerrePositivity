module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeActionSimplex
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan

/-! # 全 native 関手族による Perf の実単体的右作用
概要：元のラベル付き Perf と全関手族に、実 dg tensor 右作用を全単体的に適用する。
方針：関手族の全単体を ULift で出力宇宙へ移し、元の各単体の右作用を束ねる。
規約：Perf の対象宇宙を縮めず、Kan 入力の全高次単体を保持する。
使われ方：関手的 Perf から S•・実現・BF K の厳密豊穣作用への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]

/-- 元の全 native 関手族とラベル付き Perf の、出力宇宙を保つ実単体的右作用。 -/
def presentedPerfectDGNativeAction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D) ⊗
        (SSet.uliftFunctor.{u + 1, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFunctor A D E)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A E) where
  app _ := ↾fun p => presentedPerfectDGNativeActionSimplex A D E p.1 p.2.down
  naturality X Y f := by
    ext p
    rcases p with ⟨x, s⟩
    exact presentedPerfectDGNativeActionSimplex_pullback A D E x s.down f.unop.toOrderHom

/-- 元の実単体的右作用の各次数は、元の native tensor 単体と実右作用の合成。 -/
lemma presentedPerfectDGNativeAction_app {N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N) :
    (presentedPerfectDGNativeAction A D E).app (op ⦋N⦌) (x, ULift.up s) =
      presentedPerfectDGNativeActionSimplex A D E x s := rfl

/-- 元の実単体的右作用は、頂点で同じ厳密 dg 入力のラベル作用を回収する。 -/
lemma presentedPerfectDGNativeAction_vertex (X : PresentedPerfectDGObject A D)
    (F : DGFunctor A D E) :
    (presentedPerfectDGNativeAction A D E).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X, ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((presentedPerfectDGAction A D E F).obj X) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- 出力 Perf の宇宙へ持ち上げた、元の非離散な native Kan 入力写像空間。 -/
def presentedPerfectDGNativeParameter : SSet.{max (u + 1) v} :=
  (SSet.uliftFunctor.{u + 1, max u v}).obj (dgFunctorNativeMappingSpace A D E)

/-- 出力宇宙に移した元の入力写像空間も Kan 複体。 -/
instance presentedPerfectDGNativeParameter_kan :
    KanComplex (presentedPerfectDGNativeParameter A D E) := by
  change KanComplex ((SSet.uliftFunctor.{u + 1, max u v}).obj (dgFunctorNativeMappingSpace A D E))
  infer_instance

/-- 元の Kan 入力写像空間の全高次単体による、ラベル付き Perf の実単体的右作用。 -/
def presentedPerfectDGNativeCoreAction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D) ⊗ presentedPerfectDGNativeParameter A D E ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A E) :=
  (𝟙 _ ⊗ₘ (SSet.uliftFunctor.{u + 1, max u v}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFunctor A D E))).ι) ≫ presentedPerfectDGNativeAction A D E

/-- 元の Kan 入力写像空間から、ラベル付き Perf 間の全関手空間への実単体的射。 -/
def presentedPerfectDGNativeFamilyMap :
    presentedPerfectDGNativeParameter A D E ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A E)) :=
  curry (presentedPerfectDGNativeCoreAction A D E)

/-- 元の全関手族の curry は、評価すると元の実単体的右作用を厳密に回収する。 -/
lemma presentedPerfectDGNativeFamilyMap_uncurry :
    uncurry (presentedPerfectDGNativeFamilyMap A D E) =
      presentedPerfectDGNativeCoreAction A D E :=
  uncurry_curry _

end SerrePositivity.KST.SConstruction
