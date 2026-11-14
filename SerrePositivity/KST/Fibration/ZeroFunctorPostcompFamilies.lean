module
public import SerrePositivity.KST.Fibration.ZeroStableHomFamilies

/-! # 零値関手への全後合成族を、同じ全単体のまま元の Kan Hom へ読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 零値関手への元の後合成は、任意の実関手頂点を零値関手へ送る。 -/
theorem zeroFunctorPostcomp_vertex (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (F : B.obj ⟶ C.obj)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (v : ((ihom A.obj).obj B.obj) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((ihom A.obj).map F).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).surjective v
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ F))
  apply isZeroVertex_functorVertex_of_pointwise
  intro a
  have hz := isZeroVertex_evaluateFunctorAt hF (G.app (Opposite.op ⦋0⦌) a)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hz
  exact hz

/-- 元の全関手・全自然変換への後合成を、同じ零値全部分複体へ制限する。 -/
def zeroFunctorPostcompLift (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (F : B.obj ⟶ C.obj)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    (ihom A.obj).obj B.obj ⟶ zeroFunctorLocus A C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((ihom A.obj).map F)
    (zeroFunctorPostcomp_vertex A B C F hF)

/-- 零値部分複体への持ち上げは、周囲で同じ全後合成を厳密に回収する。 -/
theorem zeroFunctorPostcompLift_inclusion (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (F : B.obj ⟶ C.obj) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    zeroFunctorPostcompLift A B C F hF ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj C.obj) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex).ι =
      (ihom A.obj).map F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 全後合成族を、同じ全単体を保持した元の安定圏の Kan Hom として読む。 -/
def zeroFunctorPostcompStableHom (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (F : B.obj ⟶ C.obj)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    (ihom A.obj).obj B.obj ⟶ (A ⟶[SSet.{u}] C) :=
  zeroFunctorPostcompLift A B C F hF ≫ zeroFunctorLocusToStableHom A C

/-- Kan Hom を忘れると、元の全後合成族を全パラメータで厳密に回収する。 -/
theorem zeroFunctorPostcompStableHom_ambient (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (F : B.obj ⟶ C.obj) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    zeroFunctorPostcompStableHom A B C F hF ≫ stableHomAmbient A C =
      (ihom A.obj).map F := by
  rw [zeroFunctorPostcompStableHom, stableHomAmbient, ← Category.assoc,
    Category.assoc (zeroFunctorPostcompLift A B C F hF),
    zeroFunctorLocusToStableHom_inclusion, Category.assoc,
    zeroFunctorLocusToExact_inclusion]
  exact zeroFunctorPostcompLift_inclusion A B C F hF

/-- 元の後合成族の全実頂点は、同じ Kan Hom 内で零値条件を保つ。 -/
theorem zeroFunctorPostcompStableHom_zero (A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (F : B.obj ⟶ C.obj) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (v : ((ihom A.obj).obj B.obj) _⦋0⦌) :
    StableHomZeroVertex A C
      ((zeroFunctorPostcompStableHom A B C F hF).app (Opposite.op ⦋0⦌) v) :=
  zeroFunctorLocusToStableHom_zero A C
    ((zeroFunctorPostcompLift A B C F hF).app (Opposite.op ⦋0⦌) v)

end SerrePositivity.KST.Fibration
