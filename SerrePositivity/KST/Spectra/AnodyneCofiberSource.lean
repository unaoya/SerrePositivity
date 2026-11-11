module

public import SerrePositivity.KST.Spectra.AnodyneMappingLifts
public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-!
概要：anodyne 射の cofiber と、その Kan 値の点つき写像空間の相対充填。
方針：cofiber の基点包含を pushout で anodyne にし、写像空間の制限へ移す。
規約：通常の cofiber の実際の単体集合を使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。正方形の二つの三角形の比較の補助対象。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne 射の cofiber の基点包含は anodyne。
方針：元の射を一点への射に沿って pushout する。
規約：cofiber を Kan に置換する必要はない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対三角形の写像空間の充填。 -/
theorem cofiber_basepoint_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : anodyneExtensions i) :
    anodyneExtensions (PointedObject.cofiber i).hom :=
  anodyneExtensions.pushout_inr i (toUnit A) hi

/-- 概要：anodyne な基点包含を持つ源からの点つき Kan 写像空間は全境界を充填する。
方針：点への制限の RLP と点からの写像空間の終対象性を合成する。
規約：RLP は全ての単射についての実際の持ち上げを与える。
使われ方：Goerss–Jardine I §7、HTT A.3.3。三角形の充填の比較。 -/
theorem PointedMapping.terminal_rlp_of_basepoint_anodyne
    (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (hA : anodyneExtensions A.hom) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (PointedObject.basedHom A Y).right) := by
  let i : PointedObject.point ⟶ A := PointedObject.fromPoint A
  have hi : anodyneExtensions i.right := hA
  let p := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right
  let t := terminal.from (PointedObject.basedHom PointedObject.point Y).right
  have : IsIso t := isIso_of_isTerminal (homPointIsTerminal Y) terminalIsTerminal t
  have hp := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp i hi Y
  have ht := (MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso t
  have h : terminal.from (PointedObject.basedHom A Y).right = p ≫ t := Subsingleton.elim _ _
  rw [h]
  exact (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _ hp ht

/-- 概要：内側の二辺を基点へ潰した標準二単体。
方針：第二の面が欠けた二次元ホーンの cofiber を取る。
規約：欠ける面の添字は 1、残る辺は対角辺となる。
使われ方：Goerss–Jardine I §7。区間の正方形を二つの三角形で比較する補助円板。 -/
abbrev triangleDisk : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (horn.{u} 2 (1 : Fin 3)).ι

/-- 概要：相対三角形の基点包含は anodyne。
方針：ホーン包含の anodyne 性を cofiber の基点へ移す。
規約：三角形自体の Kan 性は要求しない。
使われ方：Goerss–Jardine I §7。三角形の Kan 値写像空間の充填。 -/
theorem triangleDisk_basepoint_anodyne : anodyneExtensions triangleDisk.{u}.hom :=
  cofiber_basepoint_anodyne _ (anodyneExtensions.horn_ι (1 : Fin 3))

/-- 概要：相対三角形からの Kan 値の写像空間の終対象への射は全単射に RLP を持つ。
方針：anodyne な基点包含の写像空間の制限を使う。
規約：指定した部分を保つ相対充填を与える。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の充填の比較。 -/
theorem triangleDiskHom_terminal_rlp (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (PointedObject.basedHom triangleDisk.{u} Y).right) :=
  PointedMapping.terminal_rlp_of_basepoint_anodyne _ Y triangleDisk_basepoint_anodyne

end

end SerrePositivity.KST.Spectra
