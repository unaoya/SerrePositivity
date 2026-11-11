module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityKan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex∞ と anodyne 局所化

概要：Ex∞ の単位は局所化で自然同型となり、Ex∞ は局所化可逆な射を保存・反映する。
方針：証明済みの単位の anodyne 性と自然性を使う。
規約：Moss 2020 Proposition 31 の弱同値に関する性質を、このリポジトリの anodyneQ で述べる。
使われ方：非 Kan 基底の引き戻し比較を Kan 置換へ移す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory
open SerrePositivity.SimplicialModel

/--
概要：Ex∞ は単射を保つ。
方針：有限極限保存から引き戻し保存を通して単射保存を得る。
規約：Moss 2020 Proposition 31 の単射保存。
使われ方：引き戻し比較と部分複体の置換。
-/
instance exInfinity_preservesMonomorphisms : exInfinity.{u}.PreservesMonomorphisms :=
  inferInstance

/--
概要：Ex∞ の単位の像は anodyne 局所化で可逆である。
方針：単位の anodyne 性に局所化の反転性を適用する。
規約：局所化は既存の AnodyneHomotopy.anodyneQ を使う。
使われ方：単位の自然同型の各成分。
-/
@[kerodon 00ZL]
instance exInfinityUnit_localized_isIso (X : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (exInfinityUnit.app X)) :=
  Localization.inverts _ SSet.anodyneExtensions _ (exInfinityUnit_anodyne X)

/--
概要：恒等関手と Ex∞ は anodyne 局所化へ送ると自然同型になる。
方針：単位の各成分の可逆性を束ね、自然性は単位の自然性から得る。
規約：Moss 2020 §3 の置換の弱同値の自然性。
使われ方：Ex∞ が局所化可逆な射を保存・反映すること。
-/
def exInfinityLocalizedUnitIso : AnodyneHomotopy.anodyneQ.{u} ≅
    exInfinity ⋙ AnodyneHomotopy.anodyneQ :=
  NatIso.ofComponents (fun X => asIso (AnodyneHomotopy.anodyneQ.map (exInfinityUnit.app X)))
    (by
      intro X Y f
      simpa only [Functor.comp_map, asIso_hom, Functor.id_map, ← Functor.map_comp] using
        congrArg AnodyneHomotopy.anodyneQ.map (exInfinityUnit.naturality f))

/--
概要：Ex∞ による像が局所化で可逆であることと、元の射が可逆であることは同値である。
方針：局所化後の単位の自然同型による射の可逆性の不変性を使う。
規約：Moss 2020 Proposition 31 の弱同値に関する性質。
使われ方：Kan 置換での比較から元の比較へ戻す。
-/
@[kerodon 00ZJ]
theorem exInfinity_map_localized_isIso_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (exInfinity.map f)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map f) :=
  (NatIso.isIso_map_iff exInfinityLocalizedUnitIso f).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
