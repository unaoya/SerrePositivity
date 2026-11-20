module

public import SerrePositivity.AlgebraicGeometry.PrincipalDetector

/-!
概要：KST §5 の通常のアフィン blowup の、任意の始域に対する普遍性。
方針：像中心が正則な一元で生成されるアフィン被覆上で持ち上げを構成し貼り合わせる。
規約：仮定は像イデアルの局所的な可逆性を表す環論的条件であり、因子化射を仮定しない。
使われ方：blowup の共通細分と一般スキーム上の普遍性。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R : Type u} [CommRing R] (I : Ideal R)
  {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (𝒰 : T.AffineOpenCover)

/--
概要：基底射を始域のアフィン被覆に制限した係数環準同型。
方針：Spec の充満忠実性から実際の環準同型を取り出す。
規約：KST §5、向きは R から被覆の切断環。
使われ方：像中心の局所的な正則単項生成条件。
-/
def affineCoverBaseRingMap (i : 𝒰.I₀) : R →+* 𝒰.X i :=
  (Spec.preimage (𝒰.f i ≫ f)).hom

/--
概要：被覆上の係数環準同型の Spec は元の基底射の制限。
方針：Spec の充満忠実性の逆写像の法則を使う。
規約：KST §5、基底上のスキーム射の等式。
使われ方：局所普遍写像の貼り合わせの交換式。
-/
@[simp] theorem affineCoverBaseRingMap_spec (i : 𝒰.I₀) :
    Spec.map (CommRingCat.ofHom (affineCoverBaseRingMap f 𝒰 i)) = 𝒰.f i ≫ f :=
  Spec.map_preimage _

variable (b : ∀ i, 𝒰.X i)
  (hreg : ∀ i, b i ∈ nonZeroDivisors (𝒰.X i))
  (hI : ∀ i, I.map (affineCoverBaseRingMap f 𝒰 i) = Ideal.span {b i})

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的に正則単項となる像中心から通常 blowup への普遍写像。
方針：アフィン被覆上の持ち上げを正則局所化と分離性で貼り合わせる。
規約：KST §5、始域 T はアフィンでなくてよい。
使われ方：中心を可逆化する任意のスキームからの因子化。
-/
def affineBlowupCoverLift : T ⟶ affineBlowup I :=
  𝒰.openCover.glueMorphisms
    (fun i => affineBlowupPrincipalRegularLift I (affineCoverBaseRingMap f 𝒰 i)
      (b i) (hreg i) (hI i)) (fun i j => by
      apply affineBlowup_principal_regular_overlap I (affineCoverBaseRingMap f 𝒰 i)
        (b i) (hreg i) (hI i) (𝒰.f i) (𝒰.f j)
        (affineBlowupPrincipalRegularLift I (affineCoverBaseRingMap f 𝒰 i)
          (b i) (hreg i) (hI i))
        (affineBlowupPrincipalRegularLift I (affineCoverBaseRingMap f 𝒰 j)
          (b j) (hreg j) (hI j))
      · exact affineBlowupPrincipalRegularLift_base ..
      · simp only [Category.assoc, affineBlowupPrincipalRegularLift_base,
          affineCoverBaseRingMap_spec]
        exact pullback.condition_assoc _)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン被覆で構成した普遍写像は指定された基底射を持つ。
方針：始域の開被覆で等式を検出する。
規約：KST §5、blowup の構造射との合成として述べる。
使われ方：共通細分と一般スキームの中心比較。
-/
@[reassoc] theorem affineBlowupCoverLift_base :
    affineBlowupCoverLift I f 𝒰 b hreg hI ≫ affineBlowupπ I = f := by
  apply 𝒰.openCover.hom_ext
  intro i
  simp only [affineBlowupCoverLift, Scheme.Cover.ι_glueMorphisms_assoc,
    affineBlowupPrincipalRegularLift_base, affineCoverBaseRingMap_spec]
  rfl

include b hreg hI

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的に正則単項となる像中心を持つ始域からの blowup への射は基底上で一意。
方針：アフィン被覆で正則単項中心の一意性を使う。
規約：KST §5、始域に被約性や Noether 性を要求しない。
使われ方：普遍写像の被覆・生成元の選び方への非依存性。
-/
theorem affineBlowup_cover_hom_ext {g h : T ⟶ affineBlowup I}
    (hg : g ≫ affineBlowupπ I = f) (hh : h ≫ affineBlowupπ I = f) : g = h := by
  apply 𝒰.openCover.hom_ext
  intro i
  apply affineBlowup_hom_ext_of_principal_regular I (affineCoverBaseRingMap f 𝒰 i)
    (b i) (hreg i) (hI i)
  · rw [Category.assoc, hg, affineCoverBaseRingMap_spec]
    rfl
  · rw [Category.assoc, hh, affineCoverBaseRingMap_spec]
    rfl

/--
概要：像中心を局所的に正則単項にするスキームからの持ち上げはただ一つ存在する。
方針：開被覆で構成した実際の持ち上げとその一意性を束ねる。
規約：KST §5、仮定は各環の像イデアルについてのみ述べる。
使われ方：通常 blowup の普遍性のアフィン基底版。
-/
theorem existsUnique_affineBlowup_cover_lift :
    ∃! g : T ⟶ affineBlowup I, g ≫ affineBlowupπ I = f := by
  refine ⟨affineBlowupCoverLift I f 𝒰 b hreg hI,
    affineBlowupCoverLift_base I f 𝒰 b hreg hI, ?_⟩
  intro g hg
  exact affineBlowup_cover_hom_ext I f 𝒰 b hreg hI hg
    (affineBlowupCoverLift_base I f 𝒰 b hreg hI)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
