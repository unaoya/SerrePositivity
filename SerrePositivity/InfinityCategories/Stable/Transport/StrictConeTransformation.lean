module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

/-!
分割で生成：docstring を書き直すこと
 # 元の頂点・全脚の通常の錐比較を、同じ全 coherent 錐の比較へ送る
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C}

/-- 元の頂点射・全図式の変換・全脚の可換式を、始対象を加えた通常の変換にする。 -/
def strictConeTransformation (α : F ⟶ G) (c : Cone F) (d : Cone G) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ α.app i) :
    strictConeFunctor c ⟶ strictConeFunctor d where
  app j := match j with
    | WithInitial.star => f
    | WithInitial.of j => α.app (AsSmall.down.obj j)
  naturality {j k} t := by
    cases j with
    | star =>
      cases k with
      | star =>
        change 𝟙 c.pt ≫ f = f ≫ 𝟙 d.pt
        simp only [Category.id_comp, Category.comp_id]
      | of k => exact (hf (AsSmall.down.obj k)).symm
    | of j =>
      cases k with
      | star => exact PEmpty.elim t
      | of k => exact α.naturality (AsSmall.down.map t)

/-- 同じ join の錐の形を、始対象を加えた元の通常の添字へ送る射。 -/
def strictConeShapeMap :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      nerve (WithInitial (AsSmall.{v} I)) :=
  joinMap (𝟙 Δ[0]) ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I))

end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeShapeMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictConeShapeMap := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeShapeMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeTransformation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictConeTransformation := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeTransformation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictConeTransformation._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeTransformation._proof_3

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeTransformation.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictConeTransformation.match_1 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictConeTransformation.match_1
