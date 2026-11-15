module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightPost
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopy

/-!
概要：添字関手間の指定自然変換を、BK重みのOver圏へ移す。
方針：反対圏で後合成と添字変更の間の自然変換を各成分で作る。
使われ方：HTT 4.2.4.4、RR02(a)の指定余単位の移送。
規約：反対圏での向きを保ち、元の自然変換の成分だけを使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {P Q : L ⥤ K} (α : P ⟶ Q) (e : L)

/-- 指定変換の反対射で後合成したOver関手。 -/
def overTransformationSource : Over (Opposite.op e) ⥤ Over (Opposite.op (P.obj e)) :=
  Over.post Q.op ⋙ Over.map (α.app e).op

/-- 指定自然変換の成分の反対射による、Over関手間の比較。 -/
def overTransformation : overTransformationSource α e ⟶ Over.post P.op where
  app a := Over.homMk (α.app a.left.unop).op (by
    apply Quiver.Hom.unop_inj
    exact α.naturality a.hom.unop)
  naturality a b f := by
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    exact (α.naturality f.left.unop).symm

/-- 同じ指定変換のnerveホモトピー。 -/
def overTransformationHomotopy :
    SSet.Homotopy (nerveMap (overTransformationSource α e))
      (nerveMap (Over.post P.op (X := Opposite.op e))) :=
  nerveNatTransHomotopy (overTransformation α e)

end SerrePositivity.DiagramModel.FrameWeightRealization
