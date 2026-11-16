module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingRestrictions

/-!
概要：同じtwisted arrowの全写像の二射影は、元の両端の全関手そのもの。
方針：左右の標準区間の全制限と、同じnerve反転同型の逆の評価を合成する。
規約：IS-W2 R03dの全写像の自然性・係数移送則。頂点だけの照合ではない。
使われ方：元のsource frameの射を、同じ底の正本Hom∞へ送る比較の射影式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory SSet CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)

/-- 同じ全写像の右射影は、元の標的の全nerve関手。 -/
theorem twistedPairingNerveMap_right :
    twistedPairingNerveMap A B h hh ≫ edgewiseRight (nerve C) = nerveMap B := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change Fin (n+1) ⥤ I at σ
  change SSet.yonedaEquiv (joinInr _ _ ≫ ((edgewiseWeightIso n).hom ≫
    (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h σ))) = σ ⋙ B
  rw [← Category.assoc, edgewiseWeightIso_inr, ← SSet.yonedaEquiv_naturality,
    SSet.yonedaEquiv.apply_symm_apply]
  exact twistedPairingSimplex_restrict_right A B h σ

/-- 同じ全写像の左射影は、元の始域のnerveと同じ反転同型の逆の合成。 -/
theorem twistedPairingNerveMap_left :
    twistedPairingNerveMap A B h hh ≫ edgewiseLeft (nerve C) =
      nerveMap A ≫ (nerveOppositeIso (C := C)).inv := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change Fin (n+1) ⥤ I at σ
  change (SSet.opObjEquiv (X := nerve C) (n := Opposite.op ⦋n⦌)).symm (SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫
    (joinInl _ _ ≫ ((edgewiseWeightIso n).hom ≫
      (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h σ))))) =
        (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) (σ ⋙ A)
  rw [← Category.assoc (joinInl _ _) (edgewiseWeightIso n).hom _, edgewiseWeightIso_inl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← SSet.yonedaEquiv_naturality, SSet.yonedaEquiv.apply_symm_apply]
  change (SSet.opObjEquiv (X := nerve C) (n := Opposite.op ⦋n⦌)).symm ((joinLeftOrderHom n n).monotone.functor ⋙
    twistedPairingSimplex A B h σ) = _
  rw [twistedPairingSimplex_restrict_left, nerveOppositeIso_inv_apply]

/-- 同じ全写像は、元の両端が与える指定底への射影を厳密に保つ。 -/
theorem twistedPairingNerveMap_projection :
    twistedPairingNerveMap A B h hh ≫ twistedArrowProjection (nerve C) =
      lift (nerveMap A ≫ (nerveOppositeIso (C := C)).inv) (nerveMap B) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, twistedArrowProjection_fst, lift_fst]
    exact twistedPairingNerveMap_left A B h hh
  · rw [Category.assoc, twistedArrowProjection_snd, lift_snd]
    exact twistedPairingNerveMap_right A B h hh

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
