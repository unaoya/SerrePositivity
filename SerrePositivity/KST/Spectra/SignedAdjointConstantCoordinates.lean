module

public import SerrePositivity.KST.Spectra.SignedAdjointFirstNaturality
public import SerrePositivity.KST.Spectra.PointedVerticalPathComposition

/-!
概要：符号付き比較の左端点の前後合成を、同じ二重 loop 入力と固定頂点へ照合する。
方針：交換・反転・射影の厳密自然性と定数区間の入力制限の式を用いる。
規約：元の左端点の頂点を保持。使われ方：逆三角形の定数辺の実自然性正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra
namespace PointedMapping.VerticalPath

/-- 同じ定数区間への入力制限も、合成した元の射の頂点で一定。 -/
lemma refl_pre_path {A D E : PointedSimplicialSet.{u}} (f : D ⟶ E) (i : A ⟶ D) :
    ((refl (PointedObject.toPoint E) f).pre i).path =
      SSet.const (familyVertex (i ≫ f)) := by
  change SSet.const (familyVertex f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = _
  rw [SSet.const_comp]
  exact congrArg (fun x => SSet.const x) (familyVertex_pre i f)

end PointedMapping.VerticalPath
namespace SignedAdjointPaths
open LoopExchangePaths

/-- 左端点の標的後合成は、移した実入力の同じ交換・反転・射影頂点。 -/
lemma left_post {A Y Z Z' : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (v : Z ⟶ Z') :
    left f g ≫ targetPost v =
      (input f g ≫ doublePost v) ≫ ((swap Z' ≫ reversal Z') ≫ projection Z') := by
  have hn : (swap Z ≫ reversal Z) ≫ doublePost v =
      doublePost v ≫ (swap Z' ≫ reversal Z') := by
    rw [Category.assoc, reversal_doublePost, ← Category.assoc, swap_doublePost, Category.assoc]
  have he := congrArg (fun q => (input f g ≫ q) ≫ projection Z') hn
  rw [left_eq]
  simp only [Category.assoc] at he ⊢
  rw [projection_natural]
  exact he

/-- 左端点への入力制限も、同じ合成入力と固定した交換・反転・射影頂点。 -/
lemma left_pre {A A' Y Z : PointedSimplicialSet.{u}}
    (f : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (j : A ⟶ A') :
    j ≫ left f g = (j ≫ input f g) ≫ ((swap Z ≫ reversal Z) ≫ projection Z) := by
  rw [left_eq]
  simp only [Category.assoc]

end SignedAdjointPaths
end SerrePositivity.KST.Spectra
