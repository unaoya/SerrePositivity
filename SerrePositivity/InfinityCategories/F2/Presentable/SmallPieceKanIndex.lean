module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFilteredTotalCofinal
public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftKanShapeIso

/-!
概要：部分添字への射影の左 Kan 局所添字は、元の κ に対して filtered。
方針：指定部分集合 A 内にある全空間の部分 poset と通常の左 comma を比較する。
規約：μ での余極限存在を仮定しない。上界は同じ A の κ-filtered 性で作る。
使われ方：各部分余極限の coherent な左 Kan 組立ての存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 指定部分添字 A 以下にある、元の全空間の部分 poset。 -/
def SmallFilteredTotalBelow (A : SmallFilteredPieces κ μ I) :=
  {x : SmallFilteredTotal κ μ I // x.val.1 ≤ A}

instance smallFilteredTotalBelow_partialOrder (A : SmallFilteredPieces κ μ I) :
    PartialOrder (SmallFilteredTotalBelow A) :=
  inferInstanceAs (PartialOrder {x : SmallFilteredTotal κ μ I // x.val.1 ≤ A})

/-- 左 comma の対象 poset の小さい族は、同じ A 内に上界を持つ。 -/
lemma smallFilteredTotalBelow_isCardinalFiltered (A : SmallFilteredPieces κ μ I) :
    IsCardinalFiltered (SmallFilteredTotalBelow A) κ := by
  apply isCardinalFiltered_preorder
  intro K s hK
  let f : K → A.val := fun k ↦ ⟨(s k).val.val.2, (s k).property (s k).val.property⟩
  have hK' : HasCardinalLT K κ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  have := A.property.1
  obtain ⟨j, ⟨hj⟩⟩ := IsCardinalFiltered.exists_max (κ := κ) f hK'
  refine ⟨⟨⟨⟨A, j.val⟩, j.property⟩, le_refl A⟩, fun k ↦ ?_⟩
  exact ⟨(s k).property, leOfHom (hj k)⟩

/-- 同じ下方部分 poset から、部分添字射影の通常の左 comma への関手。 -/
def smallFilteredBelowToComma (A : SmallFilteredPieces κ μ I) :
    SmallFilteredTotalBelow A ⥤ CostructuredArrow smallFilteredTotalPiece A where
  obj x := CostructuredArrow.mk (homOfLE x.property)
  map f := CostructuredArrow.homMk (homOfLE (leOfHom f)) (by subsingleton)

/-- 通常の左 comma の元の対象を、同じ下方部分 poset に戻す。 -/
def smallFilteredCommaToBelow (A : SmallFilteredPieces κ μ I) :
    CostructuredArrow smallFilteredTotalPiece A ⥤ SmallFilteredTotalBelow A where
  obj x := ⟨x.left, leOfHom x.hom⟩
  map f := homOfLE (leOfHom f.left)

/-- 同じ下方部分 poset と元の左 comma の明示的な同値。 -/
def smallFilteredBelowCommaEquivalence (A : SmallFilteredPieces κ μ I) :
    SmallFilteredTotalBelow A ≌ CostructuredArrow smallFilteredTotalPiece A where
  functor := smallFilteredBelowToComma A
  inverse := smallFilteredCommaToBelow A
  unitIso := NatIso.ofComponents (fun x ↦ eqToIso (Subtype.ext rfl))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _)
    (by subsingleton)) (fun _ ↦ by apply CostructuredArrow.hom_ext; subsingleton)

/-- 指定 A での元の native な左 Kan 添字は κ-filtered。 -/
lemma smallPiece_leftKanShape_isKappaFiltered (A : SmallFilteredPieces κ μ I) :
    IsKappaFiltered κ
      (leftKanShape (nerveMap smallFilteredTotalPiece) (nerveVertex A)) := by
  have := smallFilteredTotalBelow_isCardinalFiltered A
  have : IsKappaFiltered κ (nerve (SmallFilteredTotalBelow A)) :=
    Ind.isKappaFiltered_nerve_of_cardinalFiltered _
  have : IsKappaFiltered κ (nerve (CostructuredArrow smallFilteredTotalPiece A)) :=
    (isKappaFiltered_iff_of_equivalence
      (F1B.kanNerveQCatEquivalence (smallFilteredBelowCommaEquivalence A))).mp inferInstance
  exact (isKappaFiltered_iff_of_iso
    (F1B.kanNerveLeftKanShapeIso smallFilteredTotalPiece A)).mp inferInstance

end SerrePositivity.InfinityCategories.F2.Presentable
