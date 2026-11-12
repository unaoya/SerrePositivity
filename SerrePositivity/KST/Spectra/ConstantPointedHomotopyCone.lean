module

public import SerrePositivity.KST.Spectra.ConstantPointedHomotopyEnd
public import SerrePositivity.KST.Spectra.PointedWeightedConeUnderlying

/-!
概要：定値点つき homotopy end の標準比較を定数写像として同定する。
方針：点つき錐の比較を忘却し、通常の定値 end の比較式へ帰着する。
規約：任意の点つきパラメーターからの射に対する厳密な等式。
使われ方：Goerss–Jardine VIII §2。自明作用の hG の標準射の照合。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：定値点つき図式への全ての脚が同じ射である錐。
方針：任意の点つき射を定値図式の全成分に置く。
規約：Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。標準射とその自然性の共通の錐。 -/
def constantPointedDiagramCone (C : Type u) [SmallCategory C]
    {A X : PointedSimplicialSet.{u}} (f : A ⟶ X) : Cone ((Functor.const C).obj X) where
  pt := A
  π := { app _ := f, naturality _ _ _ := by simp }

/-- 概要：点つき定値 end の標準比較は nerve の変数に一定な射。
方針：忘却後の錐の比較を通常の定値 end の計算へ合成する。
規約：基礎単体集合の射の等式。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の標準比較の模型の固定。 -/
lemma constantPointedHomotopyEndIso_cone (C : Type u) [SmallCategory C]
    {A X : PointedSimplicialSet.{u}} (f : A ⟶ X) :
    (PointedWeightedEnd.coneComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C)
        (constantPointedDiagramCone C f)).right ≫
      (constantPointedHomotopyEndIso C X).hom.right =
        curry (snd (nerve C) A.right ≫ f.right) := by
  change _ ≫ ((PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C)
    ((Functor.const C).obj X)).hom ≫ (constantHomotopyEndIso C X.right).hom) = _
  rw [← Category.assoc, PointedWeightedEnd.underlyingIso_coneComparison]
  exact constantHomotopyEndIso_cone C f.right

namespace UnbasedPointedMapping

/-- 概要：係数の各点を源全体で一定な写像へ送る点つき射。
方針：直積の第二射影を curry し、定数基点の保存を確認する。
規約：K に基点は課さない。
使われ方：Goerss–Jardine VIII §2。自明作用の固定点への標準射。 -/
def constant (K : SSet.{u}) (X : PointedSimplicialSet.{u}) : X ⟶ obj K X :=
  Under.homMk (curry (snd K X.right)) (by
    change X.hom ≫ curry (snd K X.right) = curry (snd K (𝟙_ SSet.{u}) ≫ X.hom)
    rw [← curry_natural_left, whiskerLeft_snd])

end UnbasedPointedMapping

/-- 概要：定値錐から点つき end への標準射は定数写像への射に一致。
方針：忘却後の標準比較の式を点つき射の識別性で戻す。
規約：対象・源の Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。hG の標準射の π_* の計算の準備。 -/
lemma constantPointedHomotopyEndIso_unit (C : Type u) [SmallCategory C]
    (X : PointedSimplicialSet.{u}) :
    PointedWeightedEnd.coneComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C)
        (constantPointedDiagramCone C (𝟙 X)) ≫
      (constantPointedHomotopyEndIso C X).hom = UnbasedPointedMapping.constant (nerve C) X := by
  apply Under.UnderMorphism.ext
  change _ = curry (snd (nerve C) X.right)
  simpa only [Under.comp_right, Under.id_right, Category.comp_id] using
    constantPointedHomotopyEndIso_cone C (𝟙 X)

end

end SerrePositivity.KST.Spectra
