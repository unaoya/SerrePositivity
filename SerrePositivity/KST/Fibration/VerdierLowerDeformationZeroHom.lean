module

public import SerrePositivity.KST.Fibration.VerdierFullSLowerDeformationSource

/-!
概要：元の Stable∞ 下側三角柱の全単体で、長辺の Hom を同じ零値関手族に保つ。
方針：path 変形は元の長い Hom への前合成なので、元の全長 Hom の零値条件を使う。
規約：元の二端点を指定する。短辺や動く対角を別のものに選び直さない。
使われ方：K-6 c4 の下側全変形を、上側と同じ零値 Hom 内で制御する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：元の下側三角柱の各全単体の長い Hom は全頂点で同じ零値条件を満たす。
方針：同じ path 変形の像を元の長い Hom に代入する。
規約：全次数・全時刻単体を扱う。共有対角の固定は主張しない。
使われ方：上側との同一対角比較を構成する際の零値部分空間への制限。 -/
theorem verdierLowerDeformation_longHom_zero {n : ℕ}
    (a : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
    (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
    (j k : ULift.{u} (Fin (n + 1))) (hj : a j = ULift.up 0) (hk : a k = ULift.up 2) :
    ∀ v, StableHomZeroVertex ((verdierLowerTriangle d).obj ⟨a j⟩)
      ((verdierLowerTriangle d).obj ⟨a k⟩)
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet (verdierLowerTriangle d)).map
        ⟨j⟩ ⟨k⟩).app (Opposite.op ⦋0⦌) v) := by
  have hz : ∀ (b c : ULift.{u} (Fin 3)), b = ULift.up 0 → c = ULift.up 2 →
      ∀ w, StableHomZeroVertex ((verdierLowerTriangle d).obj ⟨b⟩)
        ((verdierLowerTriangle d).obj ⟨c⟩)
        (((verdierLowerTriangle d).map ⟨b⟩ ⟨c⟩).app (Opposite.op ⦋0⦌) w) := by
    intro b c hb hc
    subst b
    subst c
    exact verdierLowerTriangleLongHom_zero d
  intro v
  exact hz (a j) (a k) hj hk
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).map ⟨j⟩ ⟨k⟩).app (Opposite.op ⦋0⦌) v)

variable {n : ℕ}
  (a : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
  (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
  (j k : ULift.{u} (Fin (n + 1))) (hj : a j = ULift.up 0) (hk : a k = ULift.up 2)

/-- 概要：同じ全三角柱の指定した長い Hom を零値部分空間へ実際に持ち上げる。
方針：全頂点の零値条件に元の全部分複体への持ち上げを適用する。
規約：全長 Hom の射そのものを始域として保持する。
使われ方：可縮な零値 Hom 内での全パラメータ比較。 -/
def verdierLowerDeformationZeroHomLift :
    nerve (CategoryTheory.SimplicialThickening.Path j k) ⟶
      zeroFunctorLocus ((verdierLowerTriangle d).obj ⟨a j⟩)
        ((verdierLowerTriangle d).obj ⟨a k⟩) :=
  zeroStableHomFamilyLift
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet (verdierLowerTriangle d)).map ⟨j⟩ ⟨k⟩)
    (verdierLowerDeformation_longHom_zero d a t j k hj hk)

/-- 概要：零値部分空間から戻すと元の同じ三角柱の全長 Hom を厳密回収する。
方針：全部分複体への持ち上げの回収式を使う。
規約：各辺のホモトピー類だけの照合に弱めない。
使われ方：元の三角柱への指定制限。 -/
theorem verdierLowerDeformationZeroHomLift_recovery :
    verdierLowerDeformationZeroHomLift d a t j k hj hk ≫
      zeroFunctorLocusToStableHom ((verdierLowerTriangle d).obj ⟨a j⟩)
        ((verdierLowerTriangle d).obj ⟨a k⟩) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet (verdierLowerTriangle d)).map ⟨j⟩ ⟨k⟩ :=
  zeroStableHomFamilyLift_recovery _ _

/-- 概要：同じ全長 Hom の持ち上げは全正反復 S• Kan 作用後も同じ三角柱の値を回収する。
方針：元の回収等式へ同じ豊穣 Hom 作用を後合成する。
規約：元の全族を保持し、上側との貼り合わせはまだ主張しない。
使われ方：K-6 c4 の全 Ex∞ 像での零値 Hom の制御。 -/
theorem verdierLowerDeformationZeroHomLift_multi_recovery (r : ℕ) :
    (verdierLowerDeformationZeroHomLift d a t j k hj hk ≫
      zeroFunctorLocusToStableHom ((verdierLowerTriangle d).obj ⟨a j⟩)
        ((verdierLowerTriangle d).obj ⟨a k⟩)) ≫
      (stableMultiKanEnrichedFunctor r).map ((verdierLowerTriangle d).obj ⟨a j⟩)
        ((verdierLowerTriangle d).obj ⟨a k⟩) =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a t).comp SSet (verdierLowerTriangle d)).comp
        SSet (stableMultiKanEnrichedFunctor r)).map ⟨j⟩ ⟨k⟩ := by
  rw [verdierLowerDeformationZeroHomLift_recovery]
  rfl

end SerrePositivity.KST.Fibration
