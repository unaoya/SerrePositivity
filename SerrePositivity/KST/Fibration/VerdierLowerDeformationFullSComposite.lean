module
public import SerrePositivity.KST.Fibration.VerdierLowerDeformationFullSLongHom
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledTriangleInput

/-!
概要：元の下側変形の全 S• 長 Hom が、同じ合成 path の端を全時刻で保つ。
方針：元の三頂点全体の path は変形で変わらないため、同じ零値持ち上げの実点を回収する。
規約：直接 path の動く共有対角とは区別し、合成端だけを固定する。
使われ方：K-6 c4 の指定長 Hom 再構成で要求する合成端の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：元の二胞体の三頂点全体の合成 path は、元の全時刻変形で厳密に固定される。
方針：同じ全体集合に加える区間は元の全体集合を変えない。
規約：三頂点の元の path に限る。一般の path 変形 API は新設しない。
使われ方：下側の全長 Hom の合成端を回収する。 -/
theorem verdierLowerDeformation_compositePath
    (t : ULift.{u} (Fin 3) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation
      (OrderHom.id : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3)) t coherentTriangleFullPath =
      coherentTriangleFullPath := by
  rw [coherentTriangleFullPath_eq_univ]
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ (OrderHom.id : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3)) '' Set.univ ∨ _) ↔ z ∈ Set.univ
  simp

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (t : ULift.{u} (Fin 3) →o Fin 2)

/-- 概要：元の下側変形の零値持ち上げは、指定合成 path で元の同じ実点へ戻る。
方針：全体 path の厳密な固定を、元の enriched Hom の評価へ代入する。
規約：同じ零値部分空間内の実点の等号。
使われ方：全 S• 延長前の指定合成端の回収。 -/
theorem verdierLowerDeformationZeroHomLift_composite :
    (verdierLowerDeformationZeroHomLift d (OrderHom.id : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3)) t
      (ULift.up 0) (ULift.up 2) rfl rfl).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) =
      (verdierLowerTriangleZeroHomLift d).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) := by
  apply Subtype.ext
  change (stableHomAmbient _ _).app (Opposite.op ⦋0⦌)
    (((verdierLowerTriangle d).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation
          (OrderHom.id : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3)) t
          coherentTriangleFullPath))) = _
  rw [verdierLowerDeformation_compositePath]
  rfl

/-- 概要：元の全 S• 長 Hom の合成端は、全時刻で同じ元の零値作用の点となる。
方針：零値部分空間内での実点の等号を、同じ全 S• native Kan 作用へ写す。
規約：動く共有対角全体が定値であるとは主張しない。
使われ方：Ind-S (9) の指定合成端を元の下側変形へ照合する。 -/
theorem verdierLowerDeformationFullSLongHom_composite :
    (verdierLowerDeformationFullSLongHom d (OrderHom.id : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3)) t
      (ULift.up 0) (ULift.up 2) rfl rfl).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) =
      (verdierLowerTriangleZeroHomLift d ≫ zeroFunctorFullSNativeKanFamily
        ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
        ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentTriangleFullPath) := by
  exact congrArg ((zeroFunctorFullSNativeKanFamily
    ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩)
    ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)).app (Opposite.op ⦋0⦌))
      (verdierLowerDeformationZeroHomLift_composite d t)

end SerrePositivity.KST.Fibration
