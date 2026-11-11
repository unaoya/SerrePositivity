module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Ex∞ によるモノイド対象の Kan 置換

概要：有限積を保つ Ex∞ を monoidal 関手とし、内部モノイドにも適用する。
方針：Cartesian monoidal category の一般的な有限積保存からの構成を使う。
規約：Segal 1974 Proposition 1.5 の群状モノイドの bar の Kan 模型の補助。
使われ方：厳密なモノイド構造を保持したまま基礎単体集合を Kan にする。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory

/--
概要：有限積を保つ Ex∞ に標準的な monoidal 構造を付ける。
方針：Cartesian monoidal category の有限積保存からの一般構成を使う。
規約：積比較の逆同型を乗法の移送に使う。
使われ方：内部モノイドの Ex∞ による置換。
-/
instance exInfinity_monoidal : exInfinity.{u}.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts exInfinity

/--
概要：Ex∞ の単位は monoidal な自然変換である。
方針：Cartesian monoidal category の有限積保存関手の間の自然変換の一般性質を使う。
規約：恒等関手は Mathlib の標準 monoidal 構造を使う。
使われ方：元のモノイドから置換されたモノイドへの射。
-/
instance exInfinityUnit_isMonoidal : NatTrans.IsMonoidal exInfinityUnit.{u} := inferInstance

/--
概要：Ex∞ により内部モノイドを置換する関手。
方針：monoidal 関手をモノイド対象に適用する Mathlib の mapMon を使う。
規約：基礎単体集合は実際の exInfinity の値である。
使われ方：Kan な基礎単体集合を持つ群状モノイドの模型。
-/
def exInfinityMonoidFunctor : Mon SSet.{u} ⥤ Mon SSet.{u} := exInfinity.mapMon

/--
概要：内部モノイドから Ex∞ による置換への自然なモノイド射。
方針：monoidal な単位を mapMonNatTrans へ移し、恒等関手の mapMon の同型を使う。
規約：モノイドの積と単位の保存は一般的な monoidal 変換の構成から従う。
使われ方：bar の元の模型と Kan な模型の比較。
-/
def exInfinityMonoidUnit : 𝟭 (Mon SSet.{u}) ⟶ exInfinityMonoidFunctor :=
  (Functor.mapMonIdIso (C := SSet)).inv ≫ Functor.mapMonNatTrans exInfinityUnit

/--
概要：置換したモノイドの基礎単体集合は Kan 複体である。
方針：mapMon の基礎対象の定義と Ex∞ の Kan 性を使う。
規約：モノイドの群性や群状性はこの性質に不要。
使われ方：bar の行の積射影を Kan な対象で扱う。
-/
instance exInfinityMonoid_kanComplex (M : Mon SSet.{u}) :
    SSet.KanComplex (exInfinityMonoidFunctor.obj M).X :=
  exInfinity_kanComplex M.X

/--
概要：置換へのモノイド射の基礎射は、構成済みの Ex∞ の単位である。
方針：恒等関手の mapMon の同型の基礎射が恒等であることを使う。
規約：bar の比較で使う単位の向き。
使われ方：モノイド置換の基礎射の局所化での可逆性。
-/
theorem exInfinityMonoidUnit_hom (M : Mon SSet.{u}) :
    (exInfinityMonoidUnit.app M).hom = exInfinityUnit.app M.X := by
  change (𝟙 M.X) ≫ exInfinityUnit.app M.X = _
  exact Category.id_comp _

/--
概要：モノイドの置換への基礎射は anodyne 局所化で可逆である。
方針：基礎射が Ex∞ の単位であることを使う。
規約：弱同値は既存の anodyneQ で検査する。
使われ方：元の bar と Kan モノイドの bar の比較。
-/
instance exInfinityMonoidUnit_localized_isIso (M : Mon SSet.{u}) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (exInfinityMonoidUnit.app M).hom) := by
  rw [exInfinityMonoidUnit_hom]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
