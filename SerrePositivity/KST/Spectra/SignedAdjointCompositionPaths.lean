module

public import SerrePositivity.KST.Spectra.UniversalLoopExchangePaths
public import SerrePositivity.KST.Spectra.SignedAdjointComposition

/-!
概要：元の二つの随伴構造射の符号付き比較を、二つの普遍区間から構成する。
方針：交換と二回の符号反転の区間へ元の合成族を前合成し、通常の円へ制限する。
規約：区間全体の式を保持。使われ方：指定した部分パラメータの構造比較の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths

/-- 元の符号付き比較の標的。外側のみ通常の円とする。 -/
abbrev target (Z : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom PointedSimplicialSet.circle.{u}
    (PointedObject.basedHom CirclePower.space.{u} Z)

/-- 元の二つの Kan loop 値の族を合成した、二重 loop 値の族。 -/
def input {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) : A ⟶ LoopExchangePaths.doubleLoop Z :=
  f ≫ PointedObject.basedHomMap CirclePower.space.{u}
    (Y := Y) (Z := PointedObject.basedHom CirclePower.space.{u} Z) g

/-- 元の二重 loop 族の外側の円を通常の円へ戻す射影。 -/
def projection (Z : PointedSimplicialSet.{u}) : LoopExchangePaths.doubleLoop Z ⟶ target Z :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (PointedObject.basedHom CirclePower.space.{u} Z)

/-- 元の符号付き構造比較の左辺。 -/
def left {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) : A ⟶ target Z :=
  f ≫ PointedObject.basedHomMap CirclePower.space.{u}
    (Y := Y) (Z := PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} PointedSimplicialSet.circle.{u} Z).hom ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (Y := PointedObject.basedHom CirclePower.space.{u} Z)
        (Z := PointedObject.basedHom CirclePower.space.{u} Z)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z)

/-- 二つの普遍区間の共通端点。元の二度の符号反転を保持する。 -/
def middle {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) : A ⟶ target Z :=
  (input f g ≫ (LoopExchangePaths.reversal Z ≫ LoopExchangePaths.reversal Z)) ≫ projection Z

/-- 元の符号付き構造比較の右辺。 -/
def right {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) : A ⟶ target Z :=
  (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Y) ≫
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (Y := Y) (Z := PointedObject.basedHom CirclePower.space.{u} Z) g

/-- 元の左辺は、二重 loop 族の交換・符号反転・通常の円への制限そのもの。 -/
lemma left_eq {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    left f g = (input f g ≫ (LoopExchangePaths.swap Z ≫ LoopExchangePaths.reversal Z)) ≫
      projection Z := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  let C : PointedSimplicialSet.{u} := PointedSimplicialSet.circle.{u}
  let qZ := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} Z
  let qD := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (PointedObject.basedHom K Z)
  let r := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z
  let h := f ≫ (ihom K).map g
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) K CirclePower.unit.{u} Z
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change (ihom K).map qZ ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K Z).hom ≫ qD at hs
  have hc := ((MonoidalClosed.pre CirclePower.unit.{u}).naturality r).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  change qD ≫ (ihom C).map r = (ihom K).map r ≫ qD at hc
  have he : f ≫ (ihom K).map (g ≫ qZ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom ≫ (ihom C).map r =
      ((h ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K Z).hom) ≫ (ihom K).map r) ≫ qD := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc ((ihom K).map qZ) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K C Z).hom
      ((ihom C).map r), hs]
    simp only [Category.assoc]
    rw [hc]
    rfl
  dsimp only [left, input, LoopExchangePaths.swap, LoopExchangePaths.reversal, projection]
  simp only [Category.assoc] at he ⊢
  exact he

/-- 元の右辺は、二重 loop の元の族を通常の円へ制限した射そのもの。 -/
lemma right_eq {A Y Z : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    right f g = (input f g ≫ 𝟙 (LoopExchangePaths.doubleLoop Z)) ≫ projection Z := by
  have hn := ((MonoidalClosed.pre CirclePower.unit.{u}).naturality g).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  have he := congrArg (f ≫ ·) hn
  dsimp only [right, input, projection]
  simp only [Category.comp_id, Category.assoc] at he ⊢
  exact he

/-- 元の随伴比較の第一の区間。選んだ交換符号の普遍区間へ元の入力を前合成する。 -/
def firstPath {A Y Z W : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    PointedMapping.VerticalPath (PointedObject.toPoint (target Z)) (left f g) (middle f g) :=
  PointedMapping.VerticalPath.changeEndpoints
    (((LoopExchangePaths.cancellationFirst a ha).pre (input f g)).basedPost (projection Z))
    (left_eq f g) rfl

/-- 元の随伴比較の第二の区間。選んだ二回の符号反転の普遍区間を同じ入力で使う。 -/
def secondPath {A Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    PointedMapping.VerticalPath (PointedObject.toPoint (target Z)) (middle f g) (right f g) :=
  PointedMapping.VerticalPath.changeEndpoints
    (((LoopExchangePaths.reversalTwice Z).pre (input f g)).basedPost (projection Z))
    rfl (right_eq f g)

/-- 第一の区間全体は、元の入力族と同じ普遍区間・射影の合成で計算できる。 -/
lemma firstPath_h {A Y Z W : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    (firstPath a ha f g).homotopy.h = (input f g).right ▷ (Δ[1] : SSet.{u}) ≫
      (LoopExchangePaths.cancellationFirst a ha).homotopy.h ≫ (projection Z).right := by
  simp only [firstPath, PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h, Category.assoc]

/-- 第二の区間全体も、元の入力族と同じ普遍区間・射影の合成で計算できる。 -/
lemma secondPath_h {A Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    (secondPath f g).homotopy.h = (input f g).right ▷ (Δ[1] : SSet.{u}) ≫
      (LoopExchangePaths.reversalTwice Z).homotopy.h ≫ (projection Z).right := by
  simp only [secondPath, PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h, Category.assoc]

/-- 元の部分パラメータへの制限は、第一の区間全体を厳密に保持する。 -/
lemma firstPath_restriction {A B Y Z W : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (j : B ⟶ A) :
    (firstPath a ha (j ≫ f) g).homotopy.h =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ (firstPath a ha f g).homotopy.h := by
  rw [firstPath_h, firstPath_h]
  simp only [input, Under.comp_right, comp_whiskerRight, Category.assoc]

/-- 元の部分パラメータへの制限は、第二の区間全体も厳密に保持する。 -/
lemma secondPath_restriction {A B Y Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) (j : B ⟶ A) :
    (secondPath (j ≫ f) g).homotopy.h =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ (secondPath f g).homotopy.h := by
  rw [secondPath_h, secondPath_h]
  simp only [input, Under.comp_right, comp_whiskerRight, Category.assoc]

/-- 元の符号付き随伴比較を、実際の二つの基点固定区間の有限鎖として構成する。 -/
lemma chain {A Y Z W : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex W.right]
    (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z) :
    PointedMapping.VerticalChain (PointedObject.toPoint (target Z)) (left f g) (right f g) :=
  (Relation.ReflTransGen.single ⟨firstPath a ha f g⟩).trans
    (Relation.ReflTransGen.single ⟨secondPath f g⟩)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
