module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.MonoidComponentsDescent
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 成分モノイドと定数単体的モノイドの随伴

概要：実際の連結成分のモノイド関手は定数関手の左随伴である。
方針：零次の辺に関する商による降下と各単体の成分への射を互いに逆にする。
規約：KST 式 (2.3)、Lemma 2.13 の安定成分の同定のための普遍性。
使われ方：成分モノイドの余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial
namespace SimplicialMonoid

/--
概要：成分モノイドの射を元のモノイドから定数図式への射へ延ばす。
方針：成分への射と定数関手が誘導する射を合成する。
規約：各単体をその成分で評価する。
使われ方：随伴の Hom 同値の順方向。
-/
def componentsExtend {M : SimplicialObject MonCat.{u}} {N : MonCat.{u}}
    (g : componentsObject M ⟶ N) : M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj N :=
  toComponents M ≫ (Functor.const SimplexCategoryᵒᵖ).map g

/--
概要：成分に降ろした射を延ばすと元の自然変換に戻る。
方針：最初の頂点の射の自然性を各単体で評価する。
規約：全ての次数の一致を示す。
使われ方：随伴の Hom 同値の右逆性。
-/
theorem componentsExtend_desc {M : SimplicialObject MonCat.{u}} (N : MonCat.{u})
    (f : M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj N) :
    componentsExtend (MonCat.ofHom (X := componentsObject M) (Y := N)
      (componentsDesc N f)) = f := by
  apply NatTrans.ext
  funext d
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro x
  change (f.app (op ⦋0⦌)).hom
    ((M.map (SimplexCategory.const ⦋0⦌ d.unop 0).op).hom x) = (f.app d).hom x
  exact congrArg (fun t => t.hom x)
    (f.naturality (SimplexCategory.const ⦋0⦌ d.unop 0).op)

/--
概要：延ばした射を成分に降ろすと元のモノイド射に戻る。
方針：成分の元を零単体で表し、零次の成分への射の式を使う。
規約：実際の商の代表による証明。
使われ方：随伴の Hom 同値の左逆性。
-/
theorem componentsDesc_extend {M : SimplicialObject MonCat.{u}} {N : MonCat.{u}}
    (g : componentsObject M ⟶ N) : componentsDesc N (componentsExtend g) = g.hom := by
  apply MonoidHom.ext
  intro a
  induction a using π₀.rec with | mk a => ?_
  change g.hom (simplexToComponents M 0 a) = g.hom (π₀.mk a)
  rw [simplexToComponents_zero]

/--
概要：成分のモノイド射と定数図式への自然変換の Hom 同値。
方針：各次数への延長と零次からの降下を組み合わせる。
規約：定数図式への射は全てこの形で一意に表される。
使われ方：成分関手の左随伴性。
-/
def componentsHomEquiv (M : SimplicialObject MonCat.{u}) (N : MonCat.{u}) :
    (componentsObject M ⟶ N) ≃ (M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj N) where
  toFun := componentsExtend
  invFun f := MonCat.ofHom (X := componentsObject M) (Y := N) (componentsDesc N f)
  left_inv g := MonCat.hom_ext (componentsDesc_extend g)
  right_inv f := componentsExtend_desc N f

/--
概要：成分モノイドの関手は定数単体的モノイドの関手の左随伴。
方針：成分からの射の Hom 同値とその自然性を使う。
規約：追加のモデル構造は使わない。
使われ方：安定成分の余極限との交換。
-/
def componentsConstAdjunction : componentsFunctor.{u} ⊣ Functor.const SimplexCategoryᵒᵖ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := componentsHomEquiv
      homEquiv_naturality_left_symm := fun f g => by
        apply MonCat.hom_ext
        apply MonoidHom.ext
        intro a
        induction a using π₀.rec with | mk a => rfl
      homEquiv_naturality_right := fun f g => by
        change toComponents _ ≫ (Functor.const SimplexCategoryᵒᵖ).map (f ≫ g) = _
        rw [Functor.map_comp, ← Category.assoc]
        rfl }

/--
概要：成分関手の左随伴性を型クラスとして公開する。
方針：構成した随伴を登録する。
規約：成分モノイドの演算は変更しない。
使われ方：各余極限の保存の自動供給。
-/
instance componentsFunctor_isLeftAdjoint : componentsFunctor.{u}.IsLeftAdjoint :=
  componentsConstAdjunction.isLeftAdjoint

end SimplicialMonoid
end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.6.9" (partial := component) "仮定：厳密単体的モノイドの自然数順序列の実際の余極限で各項の π₀ が群（Lean が強い：k=1 の厳密模型の順序列）。結論：余極限も π₀ が群で、成分モノイド関手は定数関手の左随伴となる（順序列での閉性と π₀ の余極限保存の通常模型の部分）。全 k の空間の ∞ 余極限との比較と任意小余極限の閉性は含まれない。"] _root_.SerrePositivity.KST.Comparison.SimplicialMonoid.componentsConstAdjunction
