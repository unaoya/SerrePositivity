module
public import SerrePositivity.KST.Fibration.VerdierLowerDeformationZeroHom

/-!
概要：元の下側三角柱の零値長 Hom の持ち上げを、全ての面・退化と整合させる。
方針：F1 正本の path 変形の添字変換を使い、全部分複体への包含で厳密に照合する。
規約：元の全 Hom と同じ零値部分空間を保持し、共有対角の固定は主張しない。
使われ方：K-6 c4 の全二胞体比較へ渡す同じ零値全族の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：零値長 Hom の持ち上げは全ての添字変換に厳密に自然。
方針：同じ path 変形の再添字付けを全部分複体の包含後に適用する。
規約：時刻単体と三角形単体を同じ写像で引き戻す。
使われ方：全三角柱の面・退化と整合する零値 Hom の族。 -/
theorem verdierLowerDeformationZeroHomLift_reindex (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    {m n : ℕ} (g : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)))
    (a : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
    (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
    (j k : ULift.{u} (Fin (m + 1)))
    (hj : a (g j) = ULift.up 0) (hk : a (g k) = ULift.up 2) :
    nerveMap (SimplicialThickening.functorMap g ⟨j⟩ ⟨k⟩) ≫
        verdierLowerDeformationZeroHomLift d a t (g j) (g k) hj hk =
      verdierLowerDeformationZeroHomLift d (a.comp g) (t.comp g) j k hj hk := by
  have hp : nerveMap (SimplicialThickening.functorMap g ⟨j⟩ ⟨k⟩) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor a t (g j) (g k)) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor (a.comp g) (t.comp g) j k) := by
    apply SSet.hom_ext
    intro l
    apply ConcreteCategory.hom_ext
    intro P
    apply CategoryTheory.Functor.ext
      (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_reindex g a t (P.obj z)).symm)
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom ((verdierLowerTriangle d).obj ⟨a (g j)⟩).obj).obj
      ((verdierLowerTriangle d).obj ⟨a (g k)⟩).obj) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex).ι).1
  simp only [verdierLowerDeformationZeroHomLift, zeroStableHomFamilyLift,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  change nerveMap (SimplicialThickening.functorMap g ⟨j⟩ ⟨k⟩) ≫
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor a t (g j) (g k)) ≫
        ((verdierLowerTriangle d).map ⟨a (g j)⟩ ⟨a (g k)⟩ ≫ stableHomAmbient _ _)) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor (a.comp g) (t.comp g) j k) ≫
      ((verdierLowerTriangle d).map ⟨a (g j)⟩ ⟨a (g k)⟩ ≫ stableHomAmbient _ _)
  rw [← Category.assoc, hp]

end SerrePositivity.KST.Fibration
