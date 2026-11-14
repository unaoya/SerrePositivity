module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.FibrantRightSpanDiagram
public import SerrePositivity.EInfinity.FrameHom.ResolutionFixedRightComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CostructuredArrowPreDiagram
public import SerrePositivity.EInfinity.FrameHom.FixedRightGrothendieckInversion
public import SerrePositivity.EInfinity.FrameHom.CosimplicialHomCommaInvariance
public import SerrePositivity.EInfinity.FrameHom.GrothendieckFiberInvariance
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.TargetInvariance

/-!
概要：fibrant な全右脚上で元の Reedy 解像と全左脚を比較する。
方針：同じ固定右対象の余終性と同じ終域の Hom 不変性を全図式に適用する。
規約：元のモデル圏の全対象 fibrant は仮定せず、右終域だけを制限する。
使われ方：一般モデル圏の frame から全三本矢への実比較の弱同値性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.FibrantRightResolutionDiagram
open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 概要：元の fibrant な全右脚の終域射影の宇宙を揃える。
方針：元の射影の前後に同じ up と down を置く。
規約：全対象と全射を保つ。使われ方：小さい全図式の右変数。 -/
def smallRightForget : AsSmall.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y) ⥤
    AsSmall.{max u v} C :=
  AsSmall.down ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forget Y ⋙ AsSmall.up

/-- 概要：同じ全右脚上の元の解像の小さい Cat 値図式。
方針：元の解像の次数比較と左脚の射影を使う。
規約：全元の中間射。使われ方：固定 frame Hom の包含の不変性。 -/
abbrev resolutionDiagram := smallRightForget Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram
  (smallResolutionOverFunctor.{u, v, max u v} q ⋙
    smallResolutionLeftForget.{u, v, max u v} X)

/-- 概要：同じ全右脚上の元の全左脚の小さい Cat 値図式。
方針：元の左脚射影に対する comma を束ねる。
規約：全元の中間射と全左脚。使われ方：全三本矢の実表示。 -/
abbrev spanDiagram := smallRightForget Y ⋙
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram (smallResolutionLeftForget.{u, v, max u v} X)

/-- 概要：元の固定右対象の比較を全右脚に自然に束ねる。
方針：元の comma の前合成と後合成の厳密な交換を使う。
規約：全ての元の成分を保持。使われ方：全図式の弱比較。 -/
abbrev comparison := Functor.whiskerLeft (smallRightForget Y)
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagramPre (smallResolutionOverFunctor.{u, v, max u v} q)
    (smallResolutionLeftForget.{u, v, max u v} X))

/-- 概要：同じ全図式の Grothendieck 比較は anodyne 反転後に可逆。
方針：同じ元の分解の余終性を全図式の判定へ渡す。
規約：元の同じ比較関手。使われ方：元の全三本矢への右比較。 -/
lemma comparison_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (Grothendieck.map (comparison q Y)))) :=
  fixedRightGrothendieckComparison_localized_isIso
    (smallResolutionOverFunctor q) (smallResolutionLeftForget X) (smallRightForget Y)
    (smallResolutionOverFunctor_isLeftCofinal q)

/-- 概要：fibrant な全右脚の遷移は同じ元の Hom で反転される。
方針：両右脚の二対三と各終域の fibrancy から標的不変性を使う。
規約：元の全遷移を扱う。使われ方：固定した右脚の fiber の包含の反転。 -/
lemma hom_map_localized_isIso {s t : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y} (f : s ⟶ t) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).map f.hom.right)) := by
  have hw : weakEquivalences C f.hom.right := by
    apply (weakEquivalences C).of_precomp s.obj.hom _ s.obj.prop.2
    exact (Under.w f.hom.hom).symm ▸ t.obj.prop.2
  have : WeakEquivalence f.hom.right := ⟨hw⟩
  have : IsFibrant s.obj.right := s.property
  have : IsFibrant t.obj.right := t.property
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso q.obj q.cofibrant AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions) f.hom.right

/-- 概要：同じ小さい解像図式の全遷移の nerve は反転される。
方針：元の Hom の不変性を同じ小さい comma の表示で移す。
規約：同じ元の全図式。使われ方：固定 fiber の実包含の弱比較。 -/
lemma resolutionDiagram_map_localized_isIso
    {s t : AsSmall.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y)} (f : s ⟶ t) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap ((resolutionDiagram q Y).map f).toFunctor)) := by
  exact CosimplicialHomElements.smallCommaMap_localized_isIso.{u, v, max u v} q.obj
    (AsSmall.down.map f).hom.right
    (hom_map_localized_isIso q Y (AsSmall.down.map f))

variable [IsFibrant Y]

/-- 概要：元の恒等右脚を同じ小さい全図式の底にする。
方針：元の始対象の宇宙だけを持ち上げる。
規約：元の Y は fibrant。使われ方：全不変図式の基点。 -/
def smallInitial : AsSmall.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y) :=
  AsSmall.up.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.initial Y)

/-- 概要：同じ小さい恒等右脚は始対象。
方針：元の全右脚の唯一の射を持ち上げる。
規約：元の全射を保つ。使われ方：全図式の fiber 包含。 -/
def smallInitial_isInitial : IsInitial (smallInitial Y) :=
  IsInitial.ofUniqueHom
    (fun t => AsSmall.up.map ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.initial_isInitial Y).to
      (AsSmall.down.obj t))) (by
      intro t f
      apply ULift.ext
      exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.initial_isInitial Y).hom_ext _ _)

/-- 概要：元の全解像図式の任意の固定 fiber の実包含は反転される。
方針：元の始対象と全遷移の不変性を同じ Thomason 比較に適用する。
規約：固定 fiber 自身の Kan 性は不要。使われ方：元の frame Hom から全図式へ。 -/
lemma fiberNerveMap_localized_isIso
    (t : AsSmall.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Thomason.fiberNerveMap (resolutionDiagram q Y) t)) :=
  Thomason.fiberNerveMap_localized_isIso (resolutionDiagram q Y) (smallInitial_isInitial Y)
    (resolutionDiagram_map_localized_isIso q Y) t

end SerrePositivity.EInfinity.FrameHom.FibrantRightResolutionDiagram
