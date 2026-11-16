module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelSource

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じモデル相対圏のCAlg源を、元の全代数nerve上で全単体まで照合する。
方針：元のAsSmall.upを前合成し、同じcofibrant置換へ入る全射列を一致させる。
規約：IS-W2 R02・R03の係数移送則。頂点だけの同定で済ませない。
使われ方：同じ全strict BE図式のnative Hom関手への比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotModelUpModelCategory : _root_.HomotopicalAlgebra.ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- Homの宇宙だけ異なるAsSmallへの包含を、元の全nerve上で読む。 -/
def strictBETotModelUpNerve :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⟶
      nerve (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category where
  app _ := ↾fun s => s ⋙ AsSmall.up
  naturality _ _ _ := rfl

/-- モデル相対圏を経由した全源も、元のalgebraCAlgSourceの全単体そのもの。 -/
theorem strictBETotModelSource_up :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelUpNerve A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A = _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app n _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app n _
  apply congrArg ((_root_.SerrePositivity.EInfinity.BarrattEccles.cAlgLocalizationSource A).app n)
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => by rfl)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
