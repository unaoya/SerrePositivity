module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceBooleanMap

/-! # 元の necklace の部分集合関手と Bool 立方体関手の自然な比較
概要：元の全 necklace 射に関する Bool 座標作用を関手へ束ね、部分集合関手を回収する。
方針：同じ指示関数の順序同型と両逆律で自然性を検証する。
規約：元の全射と全頂点を保持。使われ方：数値座標の具体的な立方体関手への移送。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の非 joint 頂点を座標とする、全 necklace 上の Bool 立方体関手。 -/
def necklaceBooleanPoset : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ PartOrd where
  obj T := PartOrd.of (T.down.NonjointVertex → Bool)
  map f := PartOrd.ofHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f)
  map_id T := PartOrd.Hom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_id T)
  map_comp f g := PartOrd.Hom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_comp f g)

/-- 元の全頂点部分集合と、同じ非 joint 座標の Bool 立方体との自然な順序同型。 -/
def necklaceSubsetBooleanNatIso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetPoset.{u} ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset.{u} :=
  NatIso.ofComponents (fun T => PartOrd.Iso.mk T.down.cubeSubsetBoolIso) (by
    intro T U f
    apply PartOrd.Hom.ext
    apply DFunLike.ext
    intro s
    change U.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetMap f s) =
      U.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetMap f (T.down.cubeSubsetFromBits
        (T.down.cubeSubsetBits s)))
    erw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.cubeSubsetFromBits_bits])

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanPoset := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetBooleanNatIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSubsetBooleanNatIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetBooleanNatIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanPoset._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanPoset._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanPoset._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSubsetBooleanNatIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSubsetBooleanNatIso._proof_1
