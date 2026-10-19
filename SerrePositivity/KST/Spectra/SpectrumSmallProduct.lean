module

public import SerrePositivity.KST.Spectra.SmallProductSequenceStructure
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpectrumHomLimitFamilies

/-!
概要：任意の小さい BF Ω スペクトルの族の具体的な積と厳密な射影・普遍射。
方針：段ごとの Kan 列の積に、証明済みの単射構造と Ω 条件を与える。
規約：空積を含む。∞ 極限性は段ごとの極限性を確認して後続で公開する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1。Sp の小積。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.SmallProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u}

/-- 任意の小さい族の実際の BF Ω スペクトルの積。 -/
def obj (X : S → OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (SmallProductKanSequence.obj (fun s ↦ (X s).toKanSequence)).toOmegaSpectrum
    (SmallProductKanSequence.sigma_mono _ (fun s n ↦ (X s).sigma_mono n))
    (SmallProductKanSequence.omegaCondition _ (fun s ↦ (X s).toKanSequence_omega))

/-- 積から指定した因子への実際のスペクトル射。 -/
def projection (X : S → OmegaSpectrum.{u}) (s : S) : obj X ⟶ X s where
  app n := PointedSmallProduct.projection (fun t ↦ ((X t).level n).space) s
  comm n := (SmallProductKanSequence.sigma_projection _ n s).symm

/-- 実際のスペクトル射の族を小積への射へ束ねる。 -/
def lift {X : S → OmegaSpectrum.{u}} {A : OmegaSpectrum.{u}}
    (f : ∀ s, A ⟶ X s) : A ⟶ obj X where
  app n := PointedSmallProduct.lift (fun s ↦ (f s).app n)
  comm n := by
    apply PointedSmallProduct.hom_ext
    intro s
    change (_ ≫ (SmallProductKanSequence.obj _).sigma n) ≫ _ = _
    rw [Category.assoc, SmallProductKanSequence.sigma_projection, ← Category.assoc,
      ← whiskerLeft_comp, PointedSmallProduct.lift_projection]
    change PointedSimplicialSet.circle.{u} ◁ (f s).app n ≫ (X s).sigma n =
      (A.sigma n ≫ PointedSmallProduct.lift (fun t ↦ (f t).app (n + 1))) ≫
        PointedSmallProduct.projection (fun t ↦ ((X t).level (n + 1)).space) s
    rw [(f s).comm n, Category.assoc, PointedSmallProduct.lift_projection]

@[reassoc (attr := simp)]
lemma lift_projection {X : S → OmegaSpectrum.{u}} {A : OmegaSpectrum.{u}}
    (f : ∀ s, A ⟶ X s) (s : S) : lift f ≫ projection X s = f s :=
  OmegaSpectrum.Hom.ext (fun _ ↦ PointedSmallProduct.lift_projection _ s)

/-- 全ての射影との合成が等しければ、小積へのスペクトル射は等しい。 -/
lemma hom_ext {X : S → OmegaSpectrum.{u}} {A : OmegaSpectrum.{u}}
    {f g : A ⟶ obj X} (h : ∀ s, f ≫ projection X s = g ≫ projection X s) : f = g := by
  apply OmegaSpectrum.Hom.ext
  intro n
  apply PointedSmallProduct.hom_ext
  intro s
  exact congrArg (fun q : A ⟶ X s ↦ q.app n) (h s)

end
end SerrePositivity.KST.Spectra.OmegaSpectrum.SmallProduct
