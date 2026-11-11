module
public import SerrePositivity.KST.Fibration.RelativeSFunctor
public import SerrePositivity.KST.Fibration.RelativeSKernel

/-! # 元の包含を保つ相対 S• 四角形

core S•A → wS•(A, qf) と core S•B → wS•(B, q) の間に、
元の完全関手による可換四角形を構成する。実現後の pullback 性は別の証明課題。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- K-5 の完全関手による、元の各段の core S• の射。 -/
def coreSExactMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⟶
      simplicialSConstruction B.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp n.unop.len f.hom (exactMap_preservesSData f))
  naturality {n m} θ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (sMap A.obj θ.unop.toOrderHom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map
          (sPostcomp m.unop.len f.hom (exactMap_preservesSData f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map
          (sPostcomp n.unop.len f.hom (exactMap_preservesSData f)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (sMap B.obj θ.unop.toOrderHom)
    rw [← Functor.map_comp, ← Functor.map_comp, exactSPostcomp_reindex]

/-- 元の core 包含と相対包含は、全段・全単体作用素で可換な四角形をなす。 -/
theorem relativeSimplicialKernelSquare {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {C : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : B.obj ⟶ C) :
    CommSq (relativeSimplicialSConstructionCoreInclusion (f.hom ≫ q))
      (coreSExactMap f) (relativeSimplicialFunctorMap f q)
      (relativeSimplicialSConstructionCoreInclusion q) := by
  constructor
  apply NatTrans.ext
  funext n
  exact relativeSFunctorMap_core f q n.unop.len

end SerrePositivity.KST.Fibration
