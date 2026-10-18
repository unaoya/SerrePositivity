module

public import SerrePositivity.KST.Spectra.GroupFunctionCofaces
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
概要：加群の圏の群作用を係数とする非斉次 cochain の線形な余単体図式。
方針：自由軌道の前合成を線形写像にし、離散係数の単体集合の式から関手法則を得る。
規約：係数の環と群と加群の宇宙を揃える。
使われ方：Goerss–Jardine VIII §2。ホモトピー群の可換係数と Mathlib の非斉次 cochain 微分の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.LinearGroupCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k G : Type u} [CommRing k] [Group G]

/-- 概要：加群の群作用を離散単体集合の作用として見る。
方針：加群の忘却と離散単体集合の関手を作用へ適用する。
規約：係数の環は固定する。
使われ方：Goerss–Jardine VIII §2。関数の顔・退化の具体式の線形係数への転用。 -/
def discreteAction (A : Action (ModuleCat.{u} k) G) : Action SSet.{u} G :=
  ((Functor.const (SimplexCategoryᵒᵖ) : Type u ⥤ SSet.{u}).mapAction G).obj
    (((forget (ModuleCat.{u} k)).mapAction G).obj A)

/-- 概要：自由軌道の射が係数の関数加群に誘導する線形な前合成。
方針：軌道代表の群成分を係数の線形写像として作用させる。
規約：添字集合は反変。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の線形な顔・退化。 -/
def pre {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (A : Action (ModuleCat.{u} k) G) :
    (S → A.V) →ₗ[k] (T → A.V) where
  toFun x t := (A.ρ (θ.hom ((1 : G), t)).1).asHom.hom (x (θ.hom ((1 : G), t)).2)
  map_add' x y := by
    funext t
    exact (A.ρ (θ.hom ((1 : G), t)).1).asHom.hom.map_add _ _
  map_smul' r x := by
    funext t
    exact (A.ρ (θ.hom ((1 : G), t)).1).asHom.hom.map_smul r _

lemma pre_id (S : Type u) (A : Action (ModuleCat.{u} k) G) :
    pre (𝟙 (Action.leftRegular G ⊗ Action.trivial G S)) A = LinearMap.id := by
  ext x t
  exact congr($(NatTrans.congr_app (FreeActionFamily.functionPre_id S (discreteAction A))
    (Opposite.op ⦋0⦌)) x t)

lemma pre_comp {S T U : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S))
    (η : (Action.leftRegular G ⊗ Action.trivial G U) ⟶
      (Action.leftRegular G ⊗ Action.trivial G T)) (A : Action (ModuleCat.{u} k) G) :
    pre (η ≫ θ) A = (pre η A).comp (pre θ A) := by
  ext x t
  exact congr($(NatTrans.congr_app (FreeActionFamily.functionPre_comp θ η (discreteAction A))
    (Opposite.op ⦋0⦌)) x t)

/-- 概要：線形係数を持つ非斉次 cochain の余単体加群。
方針：自由軌道の単体的図式の射に関数加群の前合成を反変に施す。
規約：各次数は (Fin n → G) → A.V の加群。
使われ方：Goerss–Jardine VIII §2。交代余面複体と標準の群 cochain の比較。 -/
def obj (A : Action (ModuleCat.{u} k) G) : CosimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k ((Fin n.len → G) → A.V)
  map f := ModuleCat.ofHom (pre ((GroupActionCochains.freeUniversalCover G).map f.op) A)
  map_id n := by
    rw [op_id, CategoryTheory.Functor.map_id]
    change ModuleCat.ofHom (pre
      (𝟙 (Action.leftRegular G ⊗ Action.trivial G (Fin n.len → G))) A) = 𝟙 _
    rw [pre_id]
    rfl
  map_comp f g := by
    rw [op_comp, CategoryTheory.Functor.map_comp, pre_comp]
    rfl

end

end SerrePositivity.KST.Spectra.LinearGroupCochains
