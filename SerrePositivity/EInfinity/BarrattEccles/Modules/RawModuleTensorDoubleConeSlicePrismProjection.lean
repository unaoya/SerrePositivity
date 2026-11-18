module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeSlicePrism
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConePrism

/-!
概要：同じ slice 内の二重 cone prism の全射影は、元の cone prism 自身と厳密に一致する。
方針：同じ join 円柱と同じ大域射影の等式を保持する。
規約：HA Construction 1.3.1.6・1.3.1.13、全区間族の等式。使われ方：元の augmentation の全合成三角形の底条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSlicePrism_projection :
    strictRawModuleTensorDoubleConeSlicePrism A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) = strictRawModuleTensorConePrism A X P Q := by
  simp only [strictRawModuleTensorDoubleConeSlicePrism, strictRawModuleTensorConePrism, Category.assoc,
    strictRawModuleTensorDoubleConeOverJoin_projection]

end SerrePositivity.EInfinity.BarrattEccles
