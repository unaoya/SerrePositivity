module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-!
概要：関手単体集合における前後合成の可逆二胞体への作用。
方針：閉モノイダル構造の合成をもう一度 curry して単体集合の射にする。
規約：頂点ごとの同型の族を仮定せず、内部 Hom のホモトピー圏の同型を写す。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM）、§7.1.8（Tag 02X8） の比較の同値性。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：前合成そのものを関手単体集合の射として表す。
方針：内部 Hom の合成の二因子を交換して curry する。
規約：射 A→B は Fun(B,Z)→Fun(A,Z) を与える。
使われ方：Kerodon §4.5.1（Tag 01DQ） の前合成の二胞体への作用。 -/
def functorPrecompositionMap (A B Z : SSet.{u}) :
    (ihom A).obj B ⟶ (ihom ((ihom B).obj Z)).obj ((ihom A).obj Z) :=
  curry ((β_ ((ihom B).obj Z) ((ihom A).obj B)).hom ≫ MonoidalClosed.comp A B Z)

/-- 概要：後合成そのものを関手単体集合の射として表す。
方針：内部 Hom の合成を curry する。
規約：射 X→Y は Fun(K,X)→Fun(K,Y) を与える。
使われ方：Kerodon §4.5.1（Tag 01DQ） の後合成の二胞体への作用。 -/
def functorPostcompositionMap (K X Y : SSet.{u}) :
    (ihom X).obj Y ⟶ (ihom ((ihom K).obj X)).obj ((ihom K).obj Y) :=
  curry (MonoidalClosed.comp K X Y)

/-- 概要：前合成を表す射は頂点上で既存の pre に一致する。
方針：閉構造の評価と合成を次数ごとに計算する。
規約：前提となる quasicategory 性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ） の可逆二胞体の前合成。 -/
lemma functorPrecompositionMap_vertex {A B Z : SSet.{u}} (f : A ⟶ B) :
    (functorPrecompositionMap A B Z).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre f).app Z) := by
  rfl

/-- 概要：後合成を表す射は頂点上で既存の内部 Hom の map に一致する。
方針：閉構造の評価と合成を次数ごとに計算する。
規約：前提となる quasicategory 性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ） の可逆二胞体の後合成。 -/
lemma functorPostcompositionMap_vertex {K X Y : SSet.{u}} (f : X ⟶ Y) :
    (functorPostcompositionMap K X Y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((ihom K).map f) := by
  have h : curry' f ≫ functorPostcompositionMap K X Y = curry' ((ihom K).map f) := by
    unfold functorPostcompositionMap
    rw [← curry_natural_left, whiskerLeft_curry'_comp]
    rfl
  exact congrArg (SSet.unitHomEquiv _) h

/-- 概要：関手単体集合で同型な射の前合成作用は関手単体集合で同型。
方針：前合成を表す単体集合の射で同型を写す。
規約：標的 Z は任意の単体集合。
使われ方：Kerodon §4.5.1（Tag 01DQ） の前合成の同値不変性。 -/
def FunctorIso.map_pre {A B : SSet.{u}} {f g : A ⟶ B} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((pre f).app Z) ((pre g).app Z) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (functorPrecompositionMap A B Z)
  rw [functorPrecompositionMap_vertex, functorPrecompositionMap_vertex] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso (map_pre)


/-- 概要：関手単体集合で同型な射の後合成作用は関手単体集合で同型。
方針：後合成を表す単体集合の射で同型を写す。
規約：パラメーター K は任意の単体集合。
使われ方：Kerodon §4.5.1（Tag 01DQ） の関手 ∞ 圏での同値の保存。 -/
def FunctorIso.map_post {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((ihom K).map f) ((ihom K).map g) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (functorPostcompositionMap K X Y)
  rw [functorPostcompositionMap_vertex, functorPostcompositionMap_vertex] at h
  exact h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso (map_post)


/-- 概要：同値による前合成は関手 ∞ 圏の同値。
方針：逆の前合成と、元の単位・余単位の前合成作用を使う。
規約：関手の標的 Z は quasicategory。
使われ方：Kerodon Remark 4.5.1.16（Tag 01HA）、§4.6.2（Tag 01HM） の比較。 -/
def QCatEquivalence.precompose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (Z : SSet.{u}) [Quasicategory Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom Y).obj Z) ((ihom X).obj Z) where
  hom := (pre e.hom).app Z
  inv := (pre e.inv).app Z
  homInvIso := by
    simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using e.invHomIso.map_pre Z
  invHomIso := by
    simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using e.homInvIso.map_pre Z

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalence (precompose)


/-- 概要：同値による後合成は関手 ∞ 圏の同値。
方針：元の逆射と可逆二胞体を内部 Hom の後合成で写す。
規約：パラメーター K は任意の単体集合。
使われ方：Kerodon Remark 4.5.1.16（Tag 01HA）、HTT 5.1.2.2 の同値による還元。 -/
def QCatEquivalence.postcompose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom K).obj X) ((ihom K).obj Y) where
  hom := (ihom K).map e.hom
  inv := (ihom K).map e.inv
  homInvIso := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      using e.homInvIso.map_post K
  invHomIso := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      using e.invHomIso.map_post K

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalence (postcompose)


/-- 概要：同値という性質は任意の quasicategory を標的とする前合成へ移る。
方針：明示的な逆データを選び、前合成の同値を使う。
規約：元の二つの単体集合と標的 Z は quasicategory。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.2（Tag 01HM） の利用側 API。 -/
lemma IsQCatEquivalence.precompose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (Z : SSet.{u}) [Quasicategory Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre f).app Z) := he.choose.precompose Z |>.isQCatEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (precompose)


/-- 概要：同値という性質は内部 Hom の後合成へ移る。
方針：明示的な逆データを選び、後合成の同値を使う。
規約：パラメーター K は任意の単体集合。
使われ方：Kerodon §4.5.1（Tag 01DQ）、HTT 5.1.2.2 の利用側 API。 -/
lemma IsQCatEquivalence.postcompose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((ihom K).map f) := he.choose.postcompose K |>.isQCatEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (postcompose)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.1.3.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence.postcompose
