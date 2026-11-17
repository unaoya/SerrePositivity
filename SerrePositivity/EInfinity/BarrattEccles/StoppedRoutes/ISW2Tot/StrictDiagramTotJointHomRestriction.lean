module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointHomInput
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeConstant

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の二変数の正本Hom∞入力の始域制限を、既存の同じ共変Hom∞入力と合わせる。
方針：同じ反転同型の逆の定値則と、元のCAlg源・直積の二射影を計算する。
規約：IS-W2 R02〜R03の既存の反転・係数移送・合成則。二変数間の同型は仮定しない。
使われ方：両変数のcoherent比較を追加するときの、固定始域の型の厳密な照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 正本Hom∞の同じ両端入力を制限すると、元の同じ始域頂点と全標的の対になる。 -/
theorem strictBETotJointNativeHomInput_fixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A =
      lift (SSet.const (SSet.opObjEquiv.symm
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) := by
  apply CartesianMonoidalCategory.hom_ext
  · dsimp only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput]
    rw [Category.assoc, lift_fst, lift_fst]
    have hi : nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X) ≫
        nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A) =
      SSet.const (nerveVertex (Opposite.op
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj X))) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    rw [← Category.assoc, ← Category.assoc, hi,
      nerveOppositeIso_inv_const, SSet.const_comp, SSet.opFunctor_map, Equiv.apply_symm_apply]
    have hv : (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj X)) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X) :=
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_vertex A X
    exact congrArg (fun v => SSet.const (SSet.opObjEquiv.symm v)) hv
  · dsimp only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput]
    rw [Category.assoc, lift_snd, lift_snd]
    have hi : nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X) ≫
        nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A) = 𝟙 _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    rw [← Category.assoc, hi, Category.id_comp]

/-- 正本の二変数Hom∞の同じ制限は、既存の全標的の共変Hom∞そのもの。 -/
theorem strictBETotJointNativeHomCoherent_fixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X)) ≫
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomCoherent A =
    (SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) ≫
      homInfinityCovariant ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomCoherent, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput_fixSource]
  rw [homInfinityCovariant, homInfinityJointEvaluation, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun f => f ≫ twistedArrowHomInfinity (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
