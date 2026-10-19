module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed

/-!
概要：元の点つき全 Hom の後合成の厳密な合成則。
方針：全段の評価で内部 Hom の関手法則を検査する。
規約：標的は任意の Kan 列。使われ方：選択済み BF 逆射の全 Hom ホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 厳密に指定した合成列射への後合成は、同じ二つの後合成の合成。 -/
lemma pointedPost_comp_eq (A : OmegaSpectrum.{u}) {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom X Y) (g : KanSequence.Hom Y Z) (h : KanSequence.Hom X Z)
    (hh : ∀ n, f.app n ≫ g.app n = h.app n) :
    pointedPost A f ≫ pointedPost A g = pointedPost A h := by
  apply pointed_hom_ext A Z
  intro n
  simp only [Category.assoc, pointedPost_evaluation, pointedPost_evaluation_assoc]
  change pointedEvaluation A X n ≫ (ihom (A.level n).space).map (f.app n) ≫
    (ihom (A.level n).space).map (g.app n) =
    pointedEvaluation A X n ≫ (ihom (A.level n).space).map (h.app n)
  rw [← Functor.map_comp, hh]

/-- 厳密に恒等となる二列射の合成は、元の全 Hom でも恒等射となる。 -/
lemma pointedPost_comp_id (A : OmegaSpectrum.{u}) {X Y : KanSequence.{u}}
    (f : KanSequence.Hom X Y) (g : KanSequence.Hom Y X)
    (h : ∀ n, f.app n ≫ g.app n = 𝟙 _) :
    pointedPost A f ≫ pointedPost A g = 𝟙 (pointedSpace A X) := by
  apply pointed_hom_ext A X
  intro n
  simp only [Category.assoc, pointedPost_evaluation, pointedPost_evaluation_assoc,
    Category.id_comp]
  change pointedEvaluation A X n ≫ (ihom (A.level n).space).map (f.app n) ≫
    (ihom (A.level n).space).map (g.app n) = pointedEvaluation A X n
  rw [← Functor.map_comp, h]
  exact (congrArg (pointedEvaluation A X n ≫ ·)
    ((ihom (A.level n).space).map_id (X.level n).space)).trans (Category.comp_id _)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
