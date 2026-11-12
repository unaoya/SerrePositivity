module

public import SerrePositivity.KST.Spectra.ReplacedTotalization
public import Mathlib.CategoryTheory.Comma.Basic

/-!
## 概要
L9 の実際の点つき Tot への指定増強比較を構成する主経路の入口。
## 方針
増強の各成分を標準単体の変数について一定の族にし、実 Tot と Reedy 置換の単位へ送る。
## 規約
模型圏・cofibrant generation・Quillen bifunctor を仮定しない。
ここでの空間の π_* 判定を Sp の整数次数の判定と同一視しない。
## 使われ方
論文 公理 (1)、補題 3.2・3.3。τ 位相の層論を実 Tot の Čech 計算へ置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory SSet
open CategoryTheory.MonoidalClosed
open scoped MonoidalClosed
open SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.Descent.Main

/-- 概要：点つき余単体図式の増強元と指定増強（公理 (1)）。
方針：定数図式と恒等図式関手の comma 圏を使う。
規約：元の基点と全単体射を保持。使われ方：実 Tot への比較を自然に構成する定義域。 -/
abbrev AugmentedTotDiagram :=
  Comma (Functor.const SimplexCategory : PointedSimplicialSet.{u} ⥤
    CosimplicialObject PointedSimplicialSet.{u}) (𝟭 _)

/-- 概要：指定増強を標準単体の変数について一定の族にする（公理 (1)）。
方針：標準単体と増強元の積から第二射影の後に元の増強を合成する。
規約：元の図式の Reedy 条件や Kan 性は不要。使われ方：通常の実 Tot の lift への入力。 -/
def augmentationFamily (A : AugmentedTotDiagram.{u}) :
    SimplexTensorBoundary.diagram A.left.right ⟶ A.right ⋙ PointedSimplicialSet.forget where
  app j := snd (SSet.stdSimplex.obj j) A.left.right ≫ (A.hom.app j).right
  naturality i j f := by
    change (SSet.stdSimplex.map f ▷ A.left.right) ≫
      (snd _ _ ≫ (A.hom.app j).right) =
        (snd _ _ ≫ (A.hom.app i).right) ≫ (A.right.map f).right
    have h := congrArg (fun g ↦ g.right) (A.hom.naturality f)
    change (A.hom.app j).right = (A.hom.app i).right ≫ (A.right.map f).right at h
    rw [← Category.assoc, whiskerRight_snd, Category.assoc, ← h]
    rfl

/-- 概要：指定増強は元の基点を実 Tot の指定基点へ送る（公理 (1)）。
方針：lift と前合成の公式を使い、各段で元の点つき増強の基点保存を検査する。
規約：基点を後から選び直さない。使われ方：点つきの実際の指定比較。 -/
theorem augmentationFamily_basepoint (A : AugmentedTotDiagram.{u}) :
    A.left.hom ≫ CosimplicialTotalization.lift (augmentationFamily A) =
      CosimplicialTotalization.lift (PointedTotalization.basepointFamily A.right) := by
  rw [CosimplicialTotalization.lift_pre]
  congr 1
  apply NatTrans.ext
  funext j
  change (SSet.stdSimplex.obj j ◁ A.left.hom) ≫
    (snd _ _ ≫ (A.hom.app j).right) = snd _ _ ≫ (A.right.obj j).hom
  rw [← Category.assoc, whiskerLeft_snd, Category.assoc, Under.w]
  rfl

/-- 概要：指定増強から通常の実点つき Tot への指定比較（公理 (1)）。
方針：標準単体の一定な族を実 end へ lift する。
規約：対象も射も L9 の実構成。使われ方：Reedy 置換後への比較の前半。 -/
def rawTotComparison (A : AugmentedTotDiagram.{u}) : A.left ⟶ PointedTotalization.obj A.right :=
  Under.homMk (CosimplicialTotalization.lift (augmentationFamily A))
    (augmentationFamily_basepoint A)

/-- 概要：指定増強から Kan な実 Tot への指定比較（公理 (1)）。
方針：元の通常の Tot の比較に、関手的な Reedy 置換の実際の単位を後合成する。
規約：図式の各段が Kan でなくても射を定義する。使われ方：主経路の降下条件の指定写像。 -/
def totComparison (A : AugmentedTotDiagram.{u}) :
    A.left ⟶ PointedTotalization.replacementObj A.right :=
  rawTotComparison A ≫ PointedTotalization.replacementUnit.app A.right

/-- 概要：実 Tot の指定比較が全基点で π_* 同型であるという空間側の降下（公理 (1)）。
方針：L9 の Kan ホモトピー群の判定を実際の指定射に課す。
規約：増強元の Kan 性を明示する。Sp の整数次数への接続は別に行う。
使われ方：主経路の分裂・細分・有限被覆族の実際の比較。 -/
def HasTotDescent (A : AugmentedTotDiagram.{u}) [KanComplex A.left.right] : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (totComparison A).right

/-- 概要：実 Tot への指定比較は増強図式の射と可換（補題 3.2）。
方針：end の射影ごとに comma 射の可換性へ帰着する。
規約：増強元の射も元の図式の射も変更しない。
使われ方：細分・底変換で指定比較を追跡する。 -/
theorem rawTotComparison_naturality {A B : AugmentedTotDiagram.{u}} (f : A ⟶ B) :
    f.left ≫ rawTotComparison B = rawTotComparison A ≫ PointedTotalization.map f.right := by
  apply Under.UnderMorphism.ext
  apply end_.hom_ext
  intro j
  change (f.left.right ≫ CosimplicialTotalization.lift (augmentationFamily B)) ≫
    CosimplicialTotalization.π (B.right ⋙ PointedSimplicialSet.forget) j =
    (CosimplicialTotalization.lift (augmentationFamily A) ≫
      CosimplicialTotalization.map (Functor.whiskerRight f.right PointedSimplicialSet.forget)) ≫
        CosimplicialTotalization.π (B.right ⋙ PointedSimplicialSet.forget) j
  rw [Category.assoc, CosimplicialTotalization.lift_π, Category.assoc,
    CosimplicialTotalization.map_π, ← Category.assoc, CosimplicialTotalization.lift_π,
    ← curry_natural_left, ← curry_natural_right]
  apply congrArg curry
  change (SSet.stdSimplex.obj j ◁ f.left.right) ≫
    (snd _ _ ≫ (B.hom.app j).right) =
      (snd _ _ ≫ (A.hom.app j).right) ≫ (f.right.app j).right
  have h := congrArg (fun g ↦ (g.app j).right) f.w
  change f.left.right ≫ (B.hom.app j).right =
    (A.hom.app j).right ≫ (f.right.app j).right at h
  rw [← Category.assoc, whiskerLeft_snd, Category.assoc, h, Category.assoc]
  rfl

/-- 概要：Kan な実 Tot への指定比較は増強図式に自然（補題 3.2）。
方針：通常の指定比較と L9 の Reedy 置換の単位の自然性を合成する。
規約：Kan 性を自然性の仮定に加えない。使われ方：実 Tot の細分比較。 -/
theorem totComparison_naturality {A B : AugmentedTotDiagram.{u}} (f : A ⟶ B) :
    f.left ≫ totComparison B =
      totComparison A ≫ PointedTotalization.replacementMap f.right := by
  dsimp only [totComparison]
  rw [← Category.assoc, rawTotComparison_naturality, Category.assoc]
  have h := PointedTotalization.replacementUnit.naturality f.right
  change PointedTotalization.map f.right ≫ PointedTotalization.replacementUnit.app B.right =
    PointedTotalization.replacementUnit.app A.right ≫
      PointedTotalization.replacementMap f.right at h
  rw [h, ← Category.assoc]

end SerrePositivity.KST.Descent.Main
