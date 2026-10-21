module

public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptySpace

/-!
# 非空部分の余極限と元の hammock の部分単体集合との同型

概要：同じ元の包含射を非空文字列の部分単体集合への同型へ制限する。
方針：元の包含の単射性と像の完全な判定を各次数の全単射へ渡す。
規約：同型の後の包含は元の ambientMap に厳密に一致する。
使われ方：元の hammock の非空部分上の切断の反復。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def valueMap : nonemptyColimit W X Y ⟶ NonemptyValue.space W X Y where
  app n := ↾fun x => ⟨(ambientMap W X Y).app n x,
    (ambientMap_range W X Y n _).1 ⟨x, rfl⟩⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x) ((ambientMap W X Y).naturality θ)

lemma valueMap_bijective (n : SimplexCategoryᵒᵖ) : Function.Bijective ((valueMap W X Y).app n) := by
  constructor
  · intro x y h
    exact ambientMap_injective W X Y n (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (ambientMap_range W X Y n y.val).2 y.property
    exact ⟨x, Subtype.ext hx⟩

def nonemptyIso : nonemptyColimit W X Y ≅ NonemptyValue.space W X Y :=
  NatIso.ofComponents (fun n => (Equiv.ofBijective ((valueMap W X Y).app n)
    (valueMap_bijective W X Y n)).toIso) (fun θ => (valueMap W X Y).naturality θ)

lemma nonemptyIso_hom_inclusion :
    (nonemptyIso W X Y).hom ≫ NonemptyValue.inclusion W X Y = ambientMap W X Y := rfl

def nonemptyCut : NonemptyValue.space W X Y ⟶ FactorTarget.space W X Y :=
  (nonemptyIso W X Y).inv ≫ colimitCut W X Y

lemma nonemptyIso_hom_cut : (nonemptyIso W X Y).hom ≫ nonemptyCut W X Y = colimitCut W X Y := by
  rw [nonemptyCut, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma inclusion_nonemptyCut (w : Word) :
    (inclusion W X Y w ≫ (nonemptyIso W X Y).hom) ≫ nonemptyCut W X Y = cutMap W w X Y := by
  rw [Category.assoc, nonemptyIso_hom_cut, inclusion_colimitCut]

lemma inclusion_nonemptyIso_val (w : Word) {n : SimplexCategoryᵒᵖ}
    (τ : (NonemptyGraph.simplicialSet W w X Y).obj n) :
    (((inclusion W X Y w ≫ (nonemptyIso W X Y).hom).app n τ).val) =
      (graphInclusion W.paths X Y w).app n τ.val :=
  congrArg (fun k => k.app n τ) (inclusion_ambientMap W X Y w)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
