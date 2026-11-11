module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 最終頂点写像から得る Ex への自然変換

概要：単体的集合 X から Mathlib の ex(X) への自然な写像を構成する。
方針：各単体を表す写像に、細分の最終頂点写像を前合成する。
規約：Moss 2020 §3 の j:X→Ex(X)。Kan 性や単位の anodyne 性は別の証明項目。
使われ方：Ex の反復と Ex∞ の順序余極限。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite

/--
概要：各単体を最終頂点写像との合成へ送る X→Ex(X)。
方針：Ex の定義である細分された標準単体からの Hom に元を与える。
規約：Moss 2020 §3。実際の Mathlib の ex 関手を終域とする。
使われ方：反復する遷移写像の各対象での定義。
-/
@[kerodon 00YU, kerodon 00Z2]
def exUnitAt (X : SSet.{u}) : X ⟶ SSet.ex.obj X where
  app d := TypeCat.ofHom fun s =>
    ULift.up (subdivisionLastVertexAt d.unop ≫ SSet.yonedaEquiv.symm s)
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    change subdivisionLastVertexAt j.unop ≫ SSet.yonedaEquiv.symm (X.map f s) =
      SimplexCategory.sd.map f.unop ≫ subdivisionLastVertexAt i.unop ≫ SSet.yonedaEquiv.symm s
    have hy : SSet.stdSimplex.map f.unop ≫ SSet.yonedaEquiv.symm s =
        SSet.yonedaEquiv.symm (X.map f s) :=
      SSet.yonedaEquiv_symm_naturality_left f.unop s
    calc
      _ = subdivisionLastVertexAt j.unop ≫
          (SSet.stdSimplex.map f.unop ≫ SSet.yonedaEquiv.symm s) :=
        congrArg (fun k => subdivisionLastVertexAt j.unop ≫ k) hy.symm
      _ = (subdivisionLastVertexAt j.unop ≫ SSet.stdSimplex.map f.unop) ≫
          SSet.yonedaEquiv.symm s := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ SSet.yonedaEquiv.symm s)
        (subdivisionLastVertex_naturality f.unop).symm

/--
概要：最終頂点写像で定めた Ex の単位は X に関して自然である。
方針：単体を表す写像と後合成の自然性を使う。
規約：Moss 2020 §3 の反復に必要な変換。
使われ方：Ex∞ を関手として構成するための自然性。
-/
theorem exUnitAt_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ exUnitAt Y = exUnitAt X ≫ SSet.ex.map f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  change subdivisionLastVertexAt d.unop ≫ SSet.yonedaEquiv.symm (f.app d s) =
    (subdivisionLastVertexAt d.unop ≫ SSet.yonedaEquiv.symm s) ≫ f
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/--
概要：恒等関手から Ex への最終頂点による自然変換。
方針：各対象の写像とその自然性を束ねる。
規約：Moss 2020 §3。随伴の単位 id→Ex∘sd とは異なる変換。
使われ方：X→Ex(X)→Ex²(X)→… の遷移射。
-/
def exUnit : 𝟭 SSet.{u} ⟶ SSet.ex where
  app := exUnitAt
  naturality _ _ f := exUnitAt_naturality f

/--
概要：Ex の単位は単射である。
方針：各単体を表す写像に戻し、epi な最終頂点写像の前合成を打ち消す。
規約：Moss 2020 §3 の X⊆Ex(X)。anodyne 性はここでは主張しない。
使われ方：反復の単射列と、その順序余極限。
-/
instance exUnitAt_mono (X : SSet.{u}) : Mono (exUnitAt X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b h
  apply SSet.yonedaEquiv.symm.injective
  apply (cancel_epi (subdivisionLastVertexAt d.unop)).mp
  exact congrArg ULift.down h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
