module

public import SerrePositivity.KST.Spectra.SpectrumSmallProduct
public import SerrePositivity.KST.Spectra.Limits.SpectrumFiniteProducts

/-!
概要：任意の小さいスペクトルの族の具体的な積を Sp の実際の ∞ 極限錐として公開する。
方針：各段の点つき積の普遍性を全ての豊穣 Hom の普遍性へ渡し、γ3 の離散判定を適用。
規約：任意の小さい離散図式を扱い、空積も含む。有限性は仮定しない。
使われ方：HTT 4.2.4.1、HA §1.4.2。Sp の小 ∞ 極限の構成。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet

open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.SmallProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u}

/-- 元の離散図式の上の実際の積の錐。 -/
def cone (F : Discrete S ⥤ OmegaSpectrum.{u}) : Cone F where
  pt := obj (fun s ↦ F.obj (Discrete.mk s))
  π := Discrete.natTrans (fun s ↦ projection _ s.as)

/-- 積の錐の各スペクトル段は点つき単体集合の極限。 -/
def levelIsLimit (F : Discrete S ⥤ OmegaSpectrum.{u}) (n : ℕ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelCone (cone F) n) where
  lift s := PointedSmallProduct.lift (fun j ↦ s.π.app (Discrete.mk j))
  fac s j := PointedSmallProduct.lift_projection _ j.as
  uniq s m hm := by
    apply PointedSmallProduct.hom_ext
    intro j
    exact (hm (Discrete.mk j)).trans
      (PointedSmallProduct.lift_projection (fun t ↦ s.π.app (Discrete.mk t)) j).symm

/-- 具体的な小積の錐の通常の普遍性。 -/
def isLimit (F : Discrete S ⥤ OmegaSpectrum.{u}) : IsLimit (cone F) where
  lift s := lift (fun j ↦ s.π.app (Discrete.mk j))
  fac _ j := lift_projection _ j.as
  uniq s _ hm := hom_ext (fun j ↦ (hm (Discrete.mk j)).trans
    (lift_projection (fun t ↦ s.π.app (Discrete.mk t)) j).symm)

/-- 通常の厳密なスペクトルの圏にも、任意の小さい離散図式の極限が存在する。 -/
lemma hasLimitsOfShape : HasLimitsOfShape (Discrete S) OmegaSpectrum.{u} where
  has_limit F := ⟨⟨cone F, isLimit F⟩⟩

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 全ての実際の豊穣 Hom で小積錐は極限。 -/
def homIsLimit (F : Discrete S ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (cone F) X) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomCone_isLimit_of_levelwise _ (levelIsLimit F) X

/-- 構成した実際の積の錐を coherent nerve へ送る。 -/
def infinityCone (F : Discrete S ⥤ OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (cone F)

/-- 任意の小さい離散スペクトル図式の積錐は Sp の実際の ∞ 極限錐。 -/
lemma infinityCone_isLimit (F : Discrete S ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (infinityCone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit _ (homIsLimit F)

end
end SerrePositivity.KST.Spectra.OmegaSpectrum.SmallProduct
