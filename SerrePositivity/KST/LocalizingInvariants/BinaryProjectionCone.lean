module

public import SerrePositivity.KST.LocalizingInvariants.PointedProductProjection

/-!
概要：元の BF 積の第一射影の基底変換を、Sp の実極限錐として構成する。
方針：各段の点つき積の普遍性を豊穣 Hom の極限へ移し、一脚 fibration の γ3 判定を使う。
規約：底の二射と錐の頂点は元の BF 射・積。使われ方：d8 の積射影の pullback。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryProjection
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y
variable {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z) (Y : OmegaSpectrum.{u})

def ordinaryCone : PullbackCone (Binary.fst Z Y) f :=
  PullbackCone.mk (Binary.map f (𝟙 Y)) (Binary.fst X Y) (Binary.map_fst f (𝟙 Y))

def levelIsLimit (n : ℕ) : IsLimit ((spectrumLevelFunctor n).mapCone (ordinaryCone f Y)) :=
  (isLimitMapConePullbackConeEquiv (spectrumLevelFunctor n) (Binary.map_fst f (𝟙 Y))).symm
    (PointedProductProjection.isLimit (f.app n) (Y.level n).space)

def diagram : AsSmall.{u} WalkingCospan ⥤ OmegaSpectrum.{u} :=
  spectrumPullbackDiagram (Binary.fst Z Y) f

def cone : Cone (diagram f Y) := (ordinaryCone f Y).whisker AsSmall.down

def cone_levelIsLimit (n : ℕ) : IsLimit (spectrumLevelCone (cone f Y) n) :=
  (levelIsLimit f Y n).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

def homIsLimit (A : OmegaSpectrum.{u}) : IsLimit (simplicialHomCone (cone f Y) A) :=
  spectrumHomCone_isLimit_of_levelwise _ (cone_levelIsLimit f Y) A

def infinityCone : JoinCone (strictCoherentDiagram (diagram f Y)) := strictCoherentCone (cone f Y)

lemma infinityCone_isLimit : IsLimitCone (infinityCone f Y) := by
  have : ∀ A : OmegaSpectrum.{u}, Fibration
      ((simplicialHomDiagram (diagram f Y) A).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun A => by
    change Fibration
      (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op A)).map
        (Binary.fst Z Y))
    infer_instance
  exact strictCoherentCone_isLimit_of_cospan_homLimit (cone f Y) (homIsLimit f Y)

lemma infinityCone_vertex : (infinityCone f Y).vertex = coherentNerveVertex (Binary.obj X Y) :=
  strictCoherentCone_vertex _

end SerrePositivity.KST.LocalizingInvariants.BinaryProjection
