module

public import SerrePositivity.EInfinity.Hammock.WordForwardCore
public import SerrePositivity.EInfinity.Hammock.WordEmbeddingUniqueness

/-!
# forward 部分語の固定対象と一列への元の合成

概要：全方向 forward の語では元の部分語包含は同型であり、一列への射は唯一である。
方針：元の列の像の全射性と包含の一意性、Fin 1 の一意性を使う。
規約：空語の一列への射を含む。元の語の等式と包含の射を同時に回収する。
使われ方：forward 部分語で前合成した図式の余極限の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma forwardInclusion_eqToHom (a : Word) (ha : ∀ i, a.direction i = .forward) :
    ∃ h : forwardCore a = a, forwardInclusion a = eqToHom h := by
  have hr : Set.range (forwardInclusion a).orderHom = Set.range (𝟙 a : a ⟶ a).orderHom := by
    ext i
    rw [forwardInclusion_range]
    exact iff_of_true (ha i) ⟨i, rfl⟩
  obtain ⟨h, hh⟩ := embedding_eq_of_range (forwardInclusion a) (𝟙 a)
    (forwardInclusion_injective a) Function.injective_id hr
  exact ⟨h, by simpa only [Category.comp_id] using hh.symm⟩

lemma forwardInclusion_isIso (a : Word) (ha : ∀ i, a.direction i = .forward) :
    IsIso (forwardInclusion a) := by
  obtain ⟨h, he⟩ := forwardInclusion_eqToHom a ha
  rw [he]
  infer_instance

lemma forwardMap_forwardInclusion (a : Word) :
    forwardMap (forwardInclusion a) = forwardInclusion (forwardCore a) := by
  apply forwardInclusion_cancel
  exact forwardMap_fac (forwardInclusion a)

lemma forwardMap_forwardInclusion_isIso (a : Word) :
    IsIso (forwardMap (forwardInclusion a)) := by
  rw [forwardMap_forwardInclusion]
  exact forwardInclusion_isIso (forwardCore a) (forwardCore_direction a)

def forwardCollapse (a : Word) : forwardCore a ⟶ single .forward where
  orderHom := OrderHom.const _ (0 : Fin 1)
  direction_eq i := (forwardCore_direction a i).symm

lemma toSingleForward_unique {a : Word} (f g : a ⟶ single .forward) : f = g := by
  apply hom_ext
  intro i
  exact Subsingleton.elim (α := Fin 1) (f.orderHom i) (g.orderHom i)

lemma forwardCollapse_naturality {a b : Word} (f : a ⟶ b) :
    forwardMap f ≫ forwardCollapse b = forwardCollapse a := toSingleForward_unique _ _

def forwardCollapseNat : forwardFunctor ⟶ (Functor.const Word).obj (single .forward) where
  app := forwardCollapse
  naturality _ _ f := by
    change forwardMap f ≫ forwardCollapse _ = forwardCollapse _ ≫ 𝟙 _
    rw [Category.comp_id, forwardCollapse_naturality]

end SerrePositivity.EInfinity.Hammock.Word
