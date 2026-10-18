module

public import SerrePositivity.KST.Spectra.GroupFunctionCochains
public import Mathlib.Algebra.Category.Grp.Basic

/-!
概要：群の圏の作用を係数とする非斉次 cochain の余単体群の図式。
方針：自由軌道の前合成の座標式を群準同型にし、離散単体集合の式から関手法則を得る。
規約：係数の群は非可換でもよく、有限性は要求しない。
使われ方：Goerss–Jardine VIII §2。単体的群作用の π_* の cochain への比較の標的。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.GroupCoefficientCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G]

/-- 概要：群の圏の作用を離散単体集合の作用へ送る。
方針：群の忘却関手と離散単体集合の関手を作用に適用する。
規約：群演算を忘却するだけで作用を保持する。
使われ方：Goerss–Jardine VIII §2。関数の前合成の関手法則を転用する。 -/
def discreteAction (A : Action GrpCat.{u} G) : Action SSet.{u} G :=
  ((Functor.const (SimplexCategoryᵒᵖ) : Type u ⥤ SSet.{u}).mapAction G).obj
    (((forget GrpCat.{u}).mapAction G).obj A)

/-- 概要：自由軌道の射は係数の関数群への前合成の準同型を誘導する。
方針：軌道代表の群成分を係数の群準同型として適用する。
規約：添字集合の向きは反変。
使われ方：Goerss–Jardine VIII §2。cochain の顔・退化の群準同型。 -/
def pre {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (A : Action GrpCat.{u} G) :
    (S → A.V) →* (T → A.V) where
  toFun x t := (A.ρ (θ.hom ((1 : G), t)).1).asHom (x (θ.hom ((1 : G), t)).2)
  map_one' := by
    funext t
    exact (A.ρ (θ.hom ((1 : G), t)).1).asHom.hom.map_one
  map_mul' x y := by
    funext t
    exact (A.ρ (θ.hom ((1 : G), t)).1).asHom.hom.map_mul _ _

lemma pre_id (S : Type u) (A : Action GrpCat.{u} G) :
    pre (𝟙 (Action.leftRegular G ⊗ Action.trivial G S)) A = MonoidHom.id (S → A.V) := by
  ext x t
  exact congr($(NatTrans.congr_app (FreeActionFamily.functionPre_id S (discreteAction A))
    (Opposite.op ⦋0⦌)) x t)

lemma pre_comp {S T U : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S))
    (η : (Action.leftRegular G ⊗ Action.trivial G U) ⟶
      (Action.leftRegular G ⊗ Action.trivial G T)) (A : Action GrpCat.{u} G) :
    pre (η ≫ θ) A = (pre η A).comp (pre θ A) := by
  ext x t
  exact congr($(NatTrans.congr_app (FreeActionFamily.functionPre_comp θ η (discreteAction A))
    (Opposite.op ⦋0⦌)) x t)

/-- 概要：群の作用を係数とする非斉次関数群の余単体図式。
方針：自由軌道の単体的図式に反変な関数群の前合成を適用する。
規約：各次数は (Fin n → G) → A.V の群。
使われ方：Goerss–Jardine VIII §2。cochain の π_* の代数的な係数の図式。 -/
def obj (A : Action GrpCat.{u} G) : CosimplicialObject GrpCat.{u} where
  obj n := GrpCat.of ((Fin n.len → G) → A.V)
  map f := GrpCat.ofHom (pre ((GroupActionCochains.freeUniversalCover G).map f.op) A)
  map_id n := by
    rw [op_id, CategoryTheory.Functor.map_id]
    change GrpCat.ofHom (pre
      (𝟙 (Action.leftRegular G ⊗ Action.trivial G (Fin n.len → G))) A) = 𝟙 _
    rw [pre_id]
    rfl
  map_comp f g := by
    rw [op_comp, CategoryTheory.Functor.map_comp, pre_comp]
    rfl

end

end SerrePositivity.KST.Spectra.GroupCoefficientCochains
