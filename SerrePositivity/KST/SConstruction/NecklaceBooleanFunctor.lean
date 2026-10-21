module
public import SerrePositivity.KST.SConstruction.NecklaceBooleanMap

/-! # 元の necklace の部分集合関手と Bool 立方体関手の自然な比較
概要：元の全 necklace 射に関する Bool 座標作用を関手へ束ね、部分集合関手を回収する。
方針：同じ指示関数の順序同型と両逆律で自然性を検証する。
規約：元の全射と全頂点を保持。使われ方：数値座標の具体的な立方体関手への移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の非 joint 頂点を座標とする、全 necklace 上の Bool 立方体関手。 -/
def necklaceBooleanPoset : Necklace.{u} ⥤ PartOrd where
  obj T := PartOrd.of (T.down.NonjointVertex → Bool)
  map f := PartOrd.ofHom (necklaceBooleanMap f)
  map_id T := PartOrd.Hom.ext (necklaceBooleanMap_id T)
  map_comp f g := PartOrd.Hom.ext (necklaceBooleanMap_comp f g)

/-- 元の全頂点部分集合と、同じ非 joint 座標の Bool 立方体との自然な順序同型。 -/
def necklaceSubsetBooleanNatIso : necklaceSubsetPoset.{u} ≅ necklaceBooleanPoset.{u} :=
  NatIso.ofComponents (fun T => PartOrd.Iso.mk T.down.cubeSubsetBoolIso) (by
    intro T U f
    apply PartOrd.Hom.ext
    apply DFunLike.ext
    intro s
    change U.down.cubeSubsetBits (necklaceSubsetMap f s) =
      U.down.cubeSubsetBits (necklaceSubsetMap f (T.down.cubeSubsetFromBits
        (T.down.cubeSubsetBits s)))
    erw [NecklaceShape.cubeSubsetFromBits_bits])

end SerrePositivity.KST.SConstruction
