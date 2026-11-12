module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.KST.Spectra.AnodyneHomotopyEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

/-!
概要：ホーンの小対象論法による Kan 置換の点つき対象への拡張。
方針：元の基点と置換の単位を合成して新しい基点を選ぶ。
規約：基礎関手は既存の AnodyneKanReplacement。HT-KQ は使わない。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの段ごとの fibrant 置換の準備。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedKanReplacement

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SerrePositivity.SimplicialModel

/-- 概要：Kan 置換した基礎単体集合に元の基点の像を付ける。
方針：基点射と置換の自然な単位を合成する。
規約：元の対象の Kan 性は不要。
使われ方：BF 1978 §2、HTT A.3.3。点つき置換の値。 -/
def obj (X : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (X.hom ≫ AnodyneKanReplacement.unit.app X.right)

/-- 概要：点つき Kan 置換の射への作用。
方針：置換の単位の自然性と元の射の基点保存を使う。
規約：基礎射は Kan 置換関手の射への作用そのもの。
使われ方：BF 1978 §2、HTT A.3.3。段ごとの比較の自然性。 -/
def map {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  Under.homMk (AnodyneKanReplacement.functor.map f.right) (by
    change (X.hom ≫ AnodyneKanReplacement.unit.app X.right) ≫
      AnodyneKanReplacement.functor.map f.right =
        Y.hom ≫ AnodyneKanReplacement.unit.app Y.right
    rw [Category.assoc, ← AnodyneKanReplacement.unit.naturality,
      Functor.id_map, ← Category.assoc, Under.w])

/-- 概要：点つき Kan 置換の関手。
方針：基礎関手の恒等・合成法則を Under の射へ持ち上げる。
規約：基点を保存する通常の圏の関手。
使われ方：BF 1978 §2、HTT A.3.3。列の各段の置換。 -/
def functor : PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u} where
  obj := obj
  map := map
  map_id X := by
    apply Under.UnderMorphism.ext
    exact AnodyneKanReplacement.functor.map_id X.right
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact AnodyneKanReplacement.functor.map_comp f.right g.right

/-- 概要：点つき対象からその Kan 置換への自然な射。
方針：基点を単位の像として定義したことを使う。
規約：基礎射は小対象論法の anodyne 単位。
使われ方：BF 1978 §2、HTT A.3.3。置換との比較射。 -/
def unit : 𝟭 PointedSimplicialSet.{u} ⟶ functor where
  app X := Under.homMk (AnodyneKanReplacement.unit.app X.right)
  naturality {_ _} f := by
    apply Under.UnderMorphism.ext
    exact AnodyneKanReplacement.unit.naturality f.right

/-- 概要：点つき Kan 置換の単位の基礎射は anodyne。
方針：既存のホーンの小対象論法の左因子の性質を使う。
規約：弱同値クラスを用いない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。置換比較の充填。 -/
theorem unit_anodyne (X : PointedSimplicialSet.{u}) :
    SSet.anodyneExtensions (unit.app X).right := AnodyneKanReplacement.unit_anodyne X.right

/-- 概要：置換の値の基礎単体集合は Kan 複体。
方針：終対象への射のホーンの右持ち上げ性を Kan 条件へ移す。
規約：元の対象に条件を課さない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。点つき fibrant 置換の値。 -/
instance obj_kanComplex (X : PointedSimplicialSet.{u}) : KanComplex (obj X).right := by
  change Fibration (terminal.from (AnodyneKanReplacement.functor.obj X.right))
  exact (SSet.modelCategoryQuillen.fibration_iff _).2 (AnodyneKanReplacement.terminal_rlp X.right)

/-- 概要：Kan な点つき対象では置換の単位は全基点 π_* 同型。
方針：anodyne な単位と Kan な両端にホモトピー逆の定理を適用する。
規約：元の対象が Kan である場合の L9 のホモトピー類の比較。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。段の置換の比較。 -/
theorem unit_piIsomorphism (X : PointedSimplicialSet.{u}) [KanComplex X.right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := X.right) (Y := (obj X).right) (unit.app X).right :=
  kanPiIsomorphism_of_anodyne (A := X.right) (B := (obj X).right)
    (unit.app X).right (unit_anodyne X)

end

end SerrePositivity.KST.Spectra.PointedKanReplacement
