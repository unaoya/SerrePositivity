module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInput
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeConstant

/-!
概要：元の二変数の正本Hom∞入力の始域制限を、既存の同じ共変Hom∞入力と合わせる。
方針：同じ反転同型の逆の定値則と、元のCAlg源・直積の二射影を計算する。
規約：IS-W2 R02〜R03の既存の反転・係数移送・合成則。二変数間の同型は仮定しない。
使われ方：両変数のcoherent比較を追加するときの、固定始域の型の厳密な照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 正本Hom∞の同じ両端入力を制限すると、元の同じ始域頂点と全標的の対になる。 -/
theorem strictBETotJointNativeHomInput_fixSource (X : (operad A).Algebra) :
    nerveMap (strictBETotJointHomFixSource A X) ≫ strictBETotJointNativeHomInput A =
      lift (SSet.const (SSet.opObjEquiv.symm
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))
          (strictBETotModelSource A) := by
  apply CartesianMonoidalCategory.hom_ext
  · dsimp only [strictBETotJointNativeHomInput]
    rw [Category.assoc, lift_fst, lift_fst]
    have hi : nerveMap (strictBETotJointHomFixSource A X) ≫
        nerveMap (strictBETotJointHomSourceIndex A) =
      SSet.const (nerveVertex (Opposite.op
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj X))) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    rw [← Category.assoc, ← Category.assoc, hi,
      nerveOppositeIso_inv_const, SSet.const_comp, SSet.opFunctor_map, Equiv.apply_symm_apply]
    have hv : (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj X)) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X) :=
      strictBETotModelSource_vertex A X
    exact congrArg (fun v => SSet.const (SSet.opObjEquiv.symm v)) hv
  · dsimp only [strictBETotJointNativeHomInput]
    rw [Category.assoc, lift_snd, lift_snd]
    have hi : nerveMap (strictBETotJointHomFixSource A X) ≫
        nerveMap (strictBETotJointHomTargetIndex A) = 𝟙 _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    rw [← Category.assoc, hi, Category.id_comp]

/-- 正本の二変数Hom∞の同じ制限は、既存の全標的の共変Hom∞そのもの。 -/
theorem strictBETotJointNativeHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointNativeHomCoherent A =
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
      homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)) := by
  rw [strictBETotJointNativeHomCoherent, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, strictBETotJointNativeHomInput_fixSource]
  rw [homInfinityCovariant, homInfinityJointEvaluation, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun f => f ≫ twistedArrowHomInfinity (CAlg_R A))
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

end SerrePositivity.EInfinity.BarrattEccles
