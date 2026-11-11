module

public import SerrePositivity.KST.Comparison.MonoidComponentMaps
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexComponents

/-!
# 単体的モノイドの成分の実際の関手

概要：連結成分の誘導乗法を持つモノイドと自然な射を関手として構成する。
方針：既存の成分モノイドの射を使い、合成則を零単体で確認する。
規約：KST 式 (2.3)、Lemma 2.13 の安定成分の計算。
使われ方：成分関手と定数単体的モノイドの随伴。
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
概要：実際の連結成分を誘導乗法のモノイドとして束ねる。
方針：componentsMonoid を明示的な構造として MonCat に渡す。
規約：零単体の積と単位をそのまま降ろした構造。
使われ方：成分の関手の対象。
-/
def componentsObject (M : SimplicialObject MonCat.{u}) : MonCat.{u} :=
  letI := componentsMonoid M
  MonCat.of (π₀ (monoidSpace M))

/--
概要：単体的モノイドの連結成分を取る関手。
方針：既存の成分のモノイド射を使い、恒等と合成を零単体の代表で確認する。
規約：成分のモノイド構造は componentsMonoid で固定する。
使われ方：安定 rank の成分の余極限。
-/
def componentsFunctor : SimplicialObject MonCat.{u} ⥤ MonCat.{u} where
  obj := componentsObject
  map {M N} f := MonCat.ofHom (X := componentsObject M) (Y := componentsObject N)
    (componentsMap f)
  map_id M := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    induction x using π₀.rec with | mk x => rfl
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    induction x using π₀.rec with | mk x => rfl

/--
概要：零次単体から成分モノイドへの商の準同型。
方針：実際の π₀ の商写像を使い、積と単位の定義を計算する。
規約：商の積は componentsMonoid のもの。
使われ方：各次数の成分への自然な射の零次成分。
-/
def vertexToComponents (M : SimplicialObject MonCat.{u}) :
    M.obj (op ⦋0⦌) →* componentsObject M where
  toFun a := (π₀.mk a : π₀ (monoidSpace M))
  map_one' := rfl
  map_mul' _ _ := rfl

/--
概要：各次数の単体から成分モノイドへの準同型。
方針：最初の頂点へのモノイド射と零次の商写像を合成する。
規約：異なる頂点の選択の差は成分では消える。
使われ方：成分モノイドの定数図式への自然変換。
-/
def simplexToComponents (M : SimplicialObject MonCat.{u}) (n : ℕ) :
    M.obj (op ⦋n⦌) →* componentsObject M :=
  (vertexToComponents M).comp (M.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).hom

/--
概要：成分への写像は全ての面・退化と可換する。
方針：最初の頂点の成分の自然性を基礎単体集合へ適用する。
規約：単体圏の射は任意。
使われ方：成分への自然変換の構成。
-/
theorem simplexToComponents_natural (M : SimplicialObject MonCat.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (s : M.obj (op ⦋n⦌)) :
    simplexToComponents M m ((M.map f.op).hom s) = simplexToComponents M n s :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map (monoidSpace M) f s

/--
概要：元の単体的モノイドから成分の定数単体的モノイドへの自然な射。
方針：各次数の成分の準同型をまとめる。
規約：成分の自然性は全ての面・退化を含む。
使われ方：定数関手との随伴の単位の対象ごとの射。
-/
def toComponents (M : SimplicialObject MonCat.{u}) :
    M ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (componentsObject M) where
  app n := MonCat.ofHom (X := M.obj n) (Y := componentsObject M)
    (simplexToComponents M n.unop.len)
  naturality {m n} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact simplexToComponents_natural M f.unop x

end SimplicialMonoid
end SerrePositivity.KST.Comparison
