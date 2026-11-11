module
public import SerrePositivity.KST.Fibration.VerdierLowerDeformationFullSLongHom
public import SerrePositivity.KST.Fibration.VerdierLowerDeformationZeroHomFaces

/-!
概要：元の下側変形の全 S• 長 Hom は、全パラメータの単調な制限と可換である。
方針：F1 正本の path 変形の添字変更則を、同じ零値持ち上げと全 S• 作用へ送る。
規約：同じ元の path と端点を保持する。一般の path 変形 API は新設しない。
使われ方：K-6 c4 の動く長 Hom の面・退化との整合性。
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
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) {m n : ℕ}
  (a : ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin 3))
  (t : ULift.{u} (Fin (n + 1)) →o Fin 2)
  (b : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)))
  (j k : ULift.{u} (Fin (m + 1))) (hj : a (b j) = ULift.up 0)
  (hk : a (b k) = ULift.up 2)

/-- 概要：元の全 S• 長 Hom の全族も、同じパラメータの面・退化を厳密に保持する。
方針：零値持ち上げの制限等式に同じ全 S• native Kan 作用を後合成する。
規約：制限ごとに長 Hom や比較を選び直さない。
使われ方：Ind-S (9) の全パラメータ再構成への実入力の整合性。 -/
theorem verdierLowerDeformationFullSLongHom_reindex :
    nerveMap (SimplicialThickening.functorMap b ⟨j⟩ ⟨k⟩) ≫
      verdierLowerDeformationFullSLongHom d a t (b j) (b k) hj hk =
      verdierLowerDeformationFullSLongHom d (a.comp b) (t.comp b) j k hj hk := by
  simp only [verdierLowerDeformationFullSLongHom, ← Category.assoc]
  rw [verdierLowerDeformationZeroHomLift_reindex d b a t j k hj hk]
  rfl

end SerrePositivity.KST.Fibration
