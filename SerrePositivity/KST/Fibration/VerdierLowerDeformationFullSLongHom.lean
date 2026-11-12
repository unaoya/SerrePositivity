module
public import SerrePositivity.KST.Fibration.VerdierLowerDeformationZeroHom
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSNativeKanFamily

/-!
概要：元の下側全変形の長 Hom を全 S• 始域へ延長し、元の native 制限を回収する。
方針：同じ全次数・全時刻の零値 Hom の持ち上げを、既存の全 S• 零値作用へ送る。
規約：指定長 Hom の全族を保持する。上側再構成の存在は主張しない。
使われ方：K-6 c4 の動く共有対角を制御する Ind-S (9) 利用側の実入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) {n : ℕ}
  (a : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
  (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
  (j k : ULift.{u} (Fin (n + 1))) (hj : a j = ULift.up 0) (hk : a k = ULift.up 2)

/-- 概要：同じ下側全変形の指定長 Hom を、全 S• 始域の native Kan 族へ延長する。
方針：同じ零値部分空間への実持ち上げの全単体に全 S• 作用を合成する。
規約：各次数・各時刻を許す。元の対角や端点を選び直さない。
使われ方：上側再構成へ渡す動く長 Hom の実供給。 -/
def verdierLowerDeformationFullSLongHom :
    nerve (CategoryTheory.SimplicialThickening.Path j k) ⟶
      (ihom (fullSRealizationKanObject ((verdierLowerTriangle d).obj ⟨a j⟩)).obj).obj
        ((stableMultiKanEnrichedFunctor 0).obj ((verdierLowerTriangle d).obj ⟨a k⟩)).obj :=
  verdierLowerDeformationZeroHomLift d a t j k hj hk ≫
    zeroFunctorFullSNativeKanFamily ((verdierLowerTriangle d).obj ⟨a j⟩)
      ((verdierLowerTriangle d).obj ⟨a k⟩)

/-- 概要：実 core 包含で制限すると元の下側全変形の native 長 Hom を厳密に回収する。
方針：元の全 S• 零値族の制限と、同じ零値持ち上げの回収式を使う。
規約：全次数・全時刻の全 Hom 写像の等式である。
使われ方：指定全長 Hom の再構成境界に渡す元の core 制限。 -/
theorem verdierLowerDeformationFullSLongHom_core :
    verdierLowerDeformationFullSLongHom d a t j k hj hk ≫
      (pre (C := SSet.{u}) (fullSNativeCoreInclusion
        ((verdierLowerTriangle d).obj ⟨a j⟩))).app
          ((stableMultiKanEnrichedFunctor 0).obj ((verdierLowerTriangle d).obj ⟨a k⟩)).obj =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet (verdierLowerTriangle d)).comp
        SSet (stableMultiKanEnrichedFunctor 0)).map ⟨j⟩ ⟨k⟩ := by
  rw [verdierLowerDeformationFullSLongHom, Category.assoc,
    zeroFunctorFullSNativeKanFamily_core, ← Category.assoc,
    verdierLowerDeformationZeroHomLift_recovery]
  rfl

/-- 概要：二胞体の各全時刻単体では、同じ core 制限はその元の全長 Hom 自身である。
方針：構成済みの全 Hom 等式を coherent 二胞体の長 Hom 表示に読む。
規約：境界だけの照合に弱めず、動く共有対角を含む全 Hom を保持する。
使われ方：Ind-S (9) の指定長 Hom を元の実二胞体へ照合する。 -/
theorem verdierLowerDeformationFullSLongHom_triangle
    (a : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3))
    (t : ULift.{u} (Fin 3) →o Fin 2)
    (hj : a (ULift.up 0) = ULift.up 0) (hk : a (ULift.up 2) = ULift.up 2) :
    verdierLowerDeformationFullSLongHom d a t (ULift.up 0) (ULift.up 2) hj hk ≫
      (pre (C := SSet.{u}) (fullSNativeCoreInclusion
        ((verdierLowerTriangle d).obj ⟨a (ULift.up 0)⟩))).app
          ((stableMultiKanEnrichedFunctor 0).obj
            ((verdierLowerTriangle d).obj ⟨a (ULift.up 2)⟩)).obj =
      coherentTriangleLongHom (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet
        (verdierLowerTriangle d)).comp SSet (stableMultiKanEnrichedFunctor 0)) :=
  verdierLowerDeformationFullSLongHom_core d a t (ULift.up 0) (ULift.up 2) hj hk

end SerrePositivity.KST.Fibration
