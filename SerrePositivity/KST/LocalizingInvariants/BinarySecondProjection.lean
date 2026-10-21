module

public import SerrePositivity.KST.LocalizingInvariants.PointedSecondProjection
public import SerrePositivity.KST.LocalizingInvariants.BinaryProjectionSquare

/-!
概要：元の BF 積の第二射影の基底変換の実極限錐と、四辺固定の pullback 正方形。
方針：各段の第二射影の普遍性を γ3 へ渡し、元の錐の四辺を回収する。
規約：下辺は元の第二射影、左辺は id×f。使われ方：対角から graph への貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open scoped Simplicial
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinarySecondProjection
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (A B : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom A B) :=
  OmegaSpectrum.mappingSpace_kanComplex A B
variable {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z) (Y : OmegaSpectrum.{u})

instance snd_level_fibration (A B : OmegaSpectrum.{u}) (n : ℕ) :
    Fibration ((Binary.snd A B).app n).right := by
  change Fibration (CartesianMonoidalCategory.snd (A.level n).space.right (B.level n).space.right)
  exact snd_projection_fibration _ _

def ordinaryCone : PullbackCone (Binary.snd Y Z) f :=
  PullbackCone.mk (Binary.map (𝟙 Y) f) (Binary.snd Y X) (Binary.map_snd (𝟙 Y) f)

def levelIsLimit (n : ℕ) : IsLimit ((spectrumLevelFunctor n).mapCone (ordinaryCone f Y)) :=
  (isLimitMapConePullbackConeEquiv (spectrumLevelFunctor n) (Binary.map_snd (𝟙 Y) f)).symm
    (PointedSecondProjection.isLimit (f.app n) (Y.level n).space)

def diagram : AsSmall.{u} WalkingCospan ⥤ OmegaSpectrum.{u} :=
  spectrumPullbackDiagram (Binary.snd Y Z) f

def cone : Cone (diagram f Y) := (ordinaryCone f Y).whisker AsSmall.down

def homIsLimit (A : OmegaSpectrum.{u}) : IsLimit (simplicialHomCone (cone f Y) A) :=
  spectrumHomCone_isLimit_of_levelwise (cone f Y) (fun n =>
    (levelIsLimit f Y n).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm) A

lemma infinityCone_isLimit : IsLimitCone (strictCoherentCone (cone f Y)) := by
  have : ∀ A : OmegaSpectrum.{u}, Fibration
      ((simplicialHomDiagram (diagram f Y) A).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun A => by
    change Fibration
      (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op A)).map
        (Binary.snd Y Z))
    infer_instance
  exact strictCoherentCone_isLimit_of_cospan_homLimit (cone f Y) (homIsLimit f Y)

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    StrictCospanCone.square (Binary.snd Y Z) f (cone f Y)

lemma square_isPullback : IsPullbackSquare (square f Y) :=
  (isPullbackSquare_iff_transpose _).mp
    (StrictCospanCone.square_isPullback _ _ _ (infinityCone_isLimit f Y))

lemma square_bottom : squareBottomEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.snd Y X)).edge := by
  rw [square, square_transpose_bottom, StrictCospanCone.square_left]
  rfl

lemma square_left : squareLeftEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.map (𝟙 Y) f)).edge := by
  rw [square, square_transpose_left, StrictCospanCone.square_bottom]
  rfl

lemma square_right : squareRightEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (coherentNerveEdge f).edge := by
  rw [square, square_transpose_right, StrictCospanCone.square_top]

lemma square_top : squareTopEdge ≫ square f Y =
    SSet.yonedaEquiv.symm (coherentNerveEdge (Binary.snd Y Z)).edge := by
  rw [square, square_transpose_top, StrictCospanCone.square_right]

end SerrePositivity.KST.LocalizingInvariants.BinarySecondProjection
