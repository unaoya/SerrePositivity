module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordFactorization

/-!
# 元の forward 列だけを保持する部分語関手

概要：forward 列の部分語を取り、元の全ての色保存単調写像を制限する。
方針：部分語の包含への厳密な因子分解と単射性で恒等・合成を照合する。
規約：空の部分語を含む。包含は元の全列番号を保持する。
使われ方：三本矢への分数計算の比較図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore
open CategoryTheory

def forwardColumns (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Finset (Fin a.length) :=
  Finset.univ.filter (fun i => a.direction i = .forward)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardColumns)


lemma mem_forwardColumns (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin a.length) :
    i ∈ forwardColumns a ↔ a.direction i = .forward := by
  simp only [forwardColumns, Finset.mem_filter, Finset.mem_univ, true_and]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (mem_forwardColumns)


def forwardCore (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword a (forwardColumns a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardCore)


def forwardInclusion (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : forwardCore a ⟶ a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion a (forwardColumns a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardInclusion)


lemma forwardInclusion_injective (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    Function.Injective (forwardInclusion a).orderHom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective a _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardInclusion_injective)


lemma forwardInclusion_range (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin a.length) :
    i ∈ Set.range (forwardInclusion a).orderHom ↔ a.direction i = .forward := by
  change i ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion a (forwardColumns a)).orderHom ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_range]
  exact mem_forwardColumns a i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardInclusion_range)


lemma forwardCore_direction (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin (forwardCore a).length) :
    (forwardCore a).direction i = .forward := by
  exact (forwardInclusion_range a _).1 ⟨i, rfl⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardCore_direction)


def forwardMap {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) : forwardCore a ⟶ forwardCore b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (forwardInclusion b) (forwardInclusion_injective b)
    (forwardInclusion a ≫ f) (by
      rintro _ ⟨i, rfl⟩
      rw [forwardInclusion_range]
      exact (f.direction_eq _).trans (forwardCore_direction a i))).val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardMap)


lemma forwardMap_fac {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    forwardMap f ≫ forwardInclusion b = forwardInclusion a ≫ f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (forwardInclusion b) (forwardInclusion_injective b)
    (forwardInclusion a ≫ f) _).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardMap_fac)


lemma forwardInclusion_cancel {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f g : a ⟶ forwardCore b)
    (h : f ≫ forwardInclusion b = g ≫ forwardInclusion b) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  apply forwardInclusion_injective b
  exact congrArg (fun k : a ⟶ b => k.orderHom i) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardInclusion_cancel)


lemma forwardMap_id (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : forwardMap (𝟙 a) = 𝟙 (forwardCore a) := by
  apply forwardInclusion_cancel
  rw [forwardMap_fac, Category.comp_id, Category.id_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardMap_id)


lemma forwardMap_comp {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (g : b ⟶ c) :
    forwardMap (f ≫ g) = forwardMap f ≫ forwardMap g := by
  apply forwardInclusion_cancel
  rw [forwardMap_fac, Category.assoc, forwardMap_fac,
    ← Category.assoc (forwardMap f), forwardMap_fac, Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardMap_comp)


def forwardFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  obj := forwardCore
  map := forwardMap
  map_id := forwardMap_id
  map_comp := forwardMap_comp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardFunctor)


def forwardInclusionNat : forwardFunctor ⟶ 𝟭 _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  app := forwardInclusion
  naturality _ _ f := forwardMap_fac f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore (forwardInclusionNat)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore
