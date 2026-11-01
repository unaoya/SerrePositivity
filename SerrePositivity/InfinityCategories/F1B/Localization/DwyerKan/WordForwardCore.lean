module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIntersection
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordFactorization

/-!
# 元の forward 列だけを保持する部分語関手

概要：forward 列の部分語を取り、元の全ての色保存単調写像を制限する。
方針：部分語の包含への厳密な因子分解と単射性で恒等・合成を照合する。
規約：空の部分語を含む。包含は元の全列番号を保持する。
使われ方：三本矢への分数計算の比較図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

def forwardColumns (a : Word) : Finset (Fin a.length) :=
  Finset.univ.filter (fun i => a.direction i = .forward)

lemma mem_forwardColumns (a : Word) (i : Fin a.length) :
    i ∈ forwardColumns a ↔ a.direction i = .forward := by
  simp only [forwardColumns, Finset.mem_filter, Finset.mem_univ, true_and]

def forwardCore (a : Word) : Word := subword a (forwardColumns a)

def forwardInclusion (a : Word) : forwardCore a ⟶ a :=
  subwordInclusion a (forwardColumns a)

lemma forwardInclusion_injective (a : Word) :
    Function.Injective (forwardInclusion a).orderHom := subwordInclusion_injective a _

lemma forwardInclusion_range (a : Word) (i : Fin a.length) :
    i ∈ Set.range (forwardInclusion a).orderHom ↔ a.direction i = .forward := by
  change i ∈ Set.range (subwordInclusion a (forwardColumns a)).orderHom ↔ _
  rw [subwordInclusion_range]
  exact mem_forwardColumns a i

lemma forwardCore_direction (a : Word) (i : Fin (forwardCore a).length) :
    (forwardCore a).direction i = .forward := by
  exact (forwardInclusion_range a _).1 ⟨i, rfl⟩

def forwardMap {a b : Word} (f : a ⟶ b) : forwardCore a ⟶ forwardCore b :=
  (factorEmbedding (forwardInclusion b) (forwardInclusion_injective b)
    (forwardInclusion a ≫ f) (by
      rintro _ ⟨i, rfl⟩
      rw [forwardInclusion_range]
      exact (f.direction_eq _).trans (forwardCore_direction a i))).val

lemma forwardMap_fac {a b : Word} (f : a ⟶ b) :
    forwardMap f ≫ forwardInclusion b = forwardInclusion a ≫ f :=
  (factorEmbedding (forwardInclusion b) (forwardInclusion_injective b)
    (forwardInclusion a ≫ f) _).property

lemma forwardInclusion_cancel {a b : Word} (f g : a ⟶ forwardCore b)
    (h : f ≫ forwardInclusion b = g ≫ forwardInclusion b) : f = g := by
  apply hom_ext
  intro i
  apply forwardInclusion_injective b
  exact congrArg (fun k : a ⟶ b => k.orderHom i) h

lemma forwardMap_id (a : Word) : forwardMap (𝟙 a) = 𝟙 (forwardCore a) := by
  apply forwardInclusion_cancel
  rw [forwardMap_fac, Category.comp_id, Category.id_comp]

lemma forwardMap_comp {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) :
    forwardMap (f ≫ g) = forwardMap f ≫ forwardMap g := by
  apply forwardInclusion_cancel
  rw [forwardMap_fac, Category.assoc, forwardMap_fac,
    ← Category.assoc (forwardMap f), forwardMap_fac, Category.assoc]

def forwardFunctor : Word ⥤ Word where
  obj := forwardCore
  map := forwardMap
  map_id := forwardMap_id
  map_comp := forwardMap_comp

def forwardInclusionNat : forwardFunctor ⟶ 𝟭 Word where
  app := forwardInclusion
  naturality _ _ f := forwardMap_fac f

end SerrePositivity.EInfinity.Hammock.Word
