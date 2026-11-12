module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingExchange
public import SerrePositivity.KST.Spectra.RawSpectrumHomPoints
public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents

/-!
概要：全パラメータ族の転置を、元の列の構造射と源の制限へ照合する。
方針：単位頂点で内部 Hom の交換と段比較の厳密可換式を評価する。
規約：標的は任意の Kan 列。使われ方：全 Hom の符号付き loop 比較の厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 段比較の後の転置は、転置した族の実際の cotensor 構造射への合成。 -/
lemma transpose_step (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ)
    (a : A ⟶ PointedObject.basedHom (X.level n).space (Y.level n).space) :
    PointedMapping.transpose (a ≫ pointedStep X Y n) =
      PointedSimplicialSet.circle.{u} ◁ PointedMapping.transpose a ≫
        (KanSequence.mapping A Y).sigma n := by
  apply curry'_injective
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
      (Y.level (n + 1)).space).hom).1
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom]
  change curry' (PointedMapping.transpose
      (PointedMapping.transpose (a ≫ pointedStep X Y n))) = _
  rw [PointedMapping.transpose_transpose]
  have hs := homPoint_step (𝟙 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space))
    ((KanSequence.mapping A Y).sigma n) (PointedMapping.transpose a)
    (PointedSimplicialSet.circle.{u} ◁ PointedMapping.transpose a ≫
      (KanSequence.mapping A Y).sigma n) (by simp)
  rw [PointedMapping.curry'_pre, Category.id_comp] at hs
  rw [hs]
  change curry' (a ≫ pointedStep X Y n) =
    (curry' (PointedMapping.transpose a) ≫ pointedStep X (KanSequence.mapping A Y) n) ≫ _
  rw [Category.assoc]
  have he := congrArg (curry' (PointedMapping.transpose a) ≫ ·) (step_exchange X Y A n)
  refine Eq.trans ?_ he.symm
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom]
  change curry' (a ≫ pointedStep X Y n) =
    curry' (PointedMapping.transpose (PointedMapping.transpose a)) ≫
      (ihom A).map (pointedStep X Y n)
  rw [PointedMapping.transpose_transpose, curry'_ihom_map]

/-- 源の構造射への制限を転置すると、同じ構造射への前合成になる。 -/
lemma transpose_restriction (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ)
    (a : A ⟶ PointedObject.basedHom (X.level (n + 1)).space
      (Y.level (n + 1)).space) :
    PointedMapping.transpose (a ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space) =
      X.sigma n ≫ PointedMapping.transpose a := by
  apply curry'_injective
  apply (cancel_mono
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
      (Y.level (n + 1)).space).hom).1
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom]
  change curry' (PointedMapping.transpose (PointedMapping.transpose
    (a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space))) = _
  rw [PointedMapping.transpose_transpose]
  conv_rhs => rw [← PointedMapping.curry'_pre (X.sigma n) (PointedMapping.transpose a)]
  rw [Category.assoc]
  have he := congrArg (curry' (PointedMapping.transpose a) ≫ ·)
    (restriction_exchange X Y A n)
  refine Eq.trans ?_ he.symm
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom]
  change curry' (a ≫ _) =
    curry' (PointedMapping.transpose (PointedMapping.transpose a)) ≫ _
  rw [PointedMapping.transpose_transpose, curry'_ihom_map]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
