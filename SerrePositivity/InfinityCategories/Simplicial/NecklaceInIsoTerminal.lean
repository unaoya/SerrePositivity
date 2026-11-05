module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceIn
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # 元の necklace と同型な入力内の終対象
概要：入力が元の necklace の実単体集合と同型なら、その全体が固定端点図式の終対象。
方針：任意の augmentation を元の逆同型に合成し、全単体を保つ一意な可換三角形を作る。
規約：端点は元の同型で写した両端点。使われ方：標準単体上の Λ の Hom 計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory Limits _root_.Simplicial SSet

/-- 元の necklace と同型な入力内の、同じ全体を覆う necklace。 -/
def necklaceInOfIso (U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) {K : SSet.{u}} (e : U.down.carrier ≅ K) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex) where
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn.necklace := U
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn.map := e.hom
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn.map_first := rfl
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn.map_last := rfl

/-- 元の逆同型は、任意の augmentation を全体への実可換三角形へ送る。 -/
def necklaceInToOfIso (U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) {K : SSet.{u}} (e : U.down.carrier ≅ K)
    (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex)) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso U e where
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceInHom.necklaceHom :=
    { _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceHom.map := T.map ≫ e.inv
      _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceHom.map_first := (congrArg (e.inv.app _) T.map_first).trans
        (congrArg (fun f => f U.down.firstVertex) (congr_app e.hom_inv_id _))
      _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceHom.map_last := (congrArg (e.inv.app _) T.map_last).trans
        (congrArg (fun f => f U.down.lastVertex) (congr_app e.hom_inv_id _)) }
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceInHom.w := (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.map ≫ f) e.inv_hom_id).trans (Category.comp_id _))

/-- 元の全体への可換三角形は、全ての高次単体で一意。 -/
lemma necklaceInOfIso_hom_ext (U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) {K : SSet.{u}} (e : U.down.carrier ≅ K)
    {T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceIn K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex)}
    (f g : T ⟶ _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso U e) : f = g :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceHom.ext ((cancel_mono e.hom).1 (f.w.trans g.w.symm)))

/-- 元の necklace 全体は、同じ両端点を持つ元の全 necklace 図式の終対象。 -/
def necklaceInOfIso_isTerminal (U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) {K : SSet.{u}} (e : U.down.carrier ≅ K) :
    IsTerminal (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso U e) :=
  IsTerminal.ofUniqueHom (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso U e)
    (fun _ f => _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso_hom_ext U e f _)

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso_hom_ext := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso_hom_ext

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso_isTerminal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso_isTerminal := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso_isTerminal

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInToOfIso := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInOfIso_isTerminal._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInOfIso_isTerminal._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInToOfIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInToOfIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInToOfIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInToOfIso._proof_3
