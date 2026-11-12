module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed

/-! # ホモトピー圏の零対象

概要：始頂点と終頂点は h C でも始対象と終対象となる。
方針：始頂点の coslice 射影の可縮な fiber で平行辺を比較する。
規約：h C は Mathlib の hoFunctor。使われ方：S3 の Σ・Ω と零射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory Limits MonoidalCategory SSet SSet.Truncated SimplicialObject.Truncated
open scoped _root_.Simplicial

/-- 概要：零頂点は h C の零対象を与える。
方針：始頂点・終頂点から h C の射の存在と一意性を使う。
規約：同じ頂点が始対象かつ終対象。使われ方：零射と suspension/loop の構成。 -/
lemma IsZeroVertex.isZeroHo {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) : IsZero (SSet.HomotopyCategory.mk x : hoFunctor.obj X) where
  unique_to y := ⟨⟨⟨hx.1.isInitialHo.to y⟩, fun f => hx.1.isInitialHo.hom_ext f _⟩⟩
  unique_from y := ⟨⟨⟨hx.2.isTerminalHo.from y⟩, fun f => hx.2.isTerminalHo.hom_ext f _⟩⟩

/-- 概要：零頂点を持つ quasicategory のホモトピー圏は零対象を持つ。
方針：選んだ零頂点を h C に写す。
規約：安定性は不要。使われ方：h C の零射と三角構造の前提。 -/
instance hasZeroObject_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] :
    HasZeroObject (hoFunctor.obj X) where
  zero := ⟨SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex,
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero.isZeroHo⟩

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
