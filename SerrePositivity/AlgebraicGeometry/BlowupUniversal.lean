module

public import SerrePositivity.AlgebraicGeometry.PrincipalDetector
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway

/-!
概要：KST §5、Stacks 080Y の一般スキーム上の通常 blowup の普遍写像。
方針：基底のアフィン開集合に入る始域のアフィン被覆上で正則単項持ち上げを貼り合わせる。
規約：局所条件は環準同型と像イデアルだけで述べ、因子化射の存在を仮定しない。
使われ方：可逆中心に対する blowup の普遍性と合成の支配。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X T : Scheme.{u}} (I : X.IdealSheafData) (f : T ⟶ X)
  (𝒰 : T.AffineOpenCover) (V : 𝒰.I₀ → X.affineOpens)
  (φ : ∀ i, Γ(X, (V i).1) →+* 𝒰.X i)
  (b : ∀ i, 𝒰.X i)
  (hreg : ∀ i, b i ∈ nonZeroDivisors (𝒰.X i))
  (hI : ∀ i, (I.ideal (V i)).map (φ i) = Ideal.span {b i})
  (hbase : ∀ i, Spec.map (CommRingCat.ofHom (φ i)) ≫ (V i).2.fromSpec = 𝒰.f i ≫ f)

/--
概要：一般の基底の一つのアフィン開集合上での局所普遍写像。
方針：正則単項中心からのアフィン blowup への射と局所モデルの標準射を合成する。
規約：KST §5、Stacks 080Y、標的は一般スキーム上の実際の blowup。
使われ方：大域普遍写像のアフィン局所成分。
-/
def blowupUniversalLocalLift (i : 𝒰.I₀) : Spec (𝒰.X i) ⟶ blowup I :=
  affineBlowupPrincipalRegularLift (I.ideal (V i)) (φ i) (b i) (hreg i) (hI i) ≫
    blowupAffineι I (V i)

include hI hbase

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の基底上の局所普遍写像は指定された基底射と両立する。
方針：局所モデルの構造射とアフィン普遍写像の係数保存を使う。
規約：KST §5、Stacks 080Y、X への射の等式。
使われ方：局所普遍写像の重なり上の一致。
-/
@[reassoc] theorem blowupUniversalLocalLift_base (i : 𝒰.I₀) :
    blowupUniversalLocalLift I 𝒰 V φ b hreg hI i ≫ blowupπ I = 𝒰.f i ≫ f := by
  unfold blowupUniversalLocalLift
  rw [Category.assoc, blowupAffineι_π]
  change affineBlowupPrincipalRegularLift (I.ideal (V i)) (φ i) (b i) (hreg i) (hI i) ≫
    (affineBlowupπ (I.ideal (V i)) ≫ (V i).2.fromSpec) = _
  rw [← Category.assoc, affineBlowupPrincipalRegularLift_base]
  exact hbase i

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的な正則生成元の局所化は一般基底の中心の外を検出する。
方針：アフィンの中心外検出を fromSpec による中心外開集合の逆像公式で移す。
規約：KST §5、Stacks 080Y、正則性は零核にのみ別途必要。
使われ方：大域普遍写像の貼り合わせと一意性。
-/
theorem blowupUniversal_detector_range (i : 𝒰.I₀) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap (𝒰.X i)
        (Localization.Away (b i)))) ≫ 𝒰.f i ≫ f) ⊆ (centerComplement I).carrier := by
  rw [← hbase i, ← Category.assoc]
  rintro _ ⟨x, rfl⟩
  have hx := principalDetector_range_complement (I.ideal (V i)) (φ i) (b i)
    ((hI i).symm ▸ Ideal.subset_span (Set.mem_singleton (b i))) ⟨x, rfl⟩
  rw [← fromSpec_preimage_centerComplement I (V i)] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
/--
概要：像中心が局所的に正則単項となる射から一般の blowup への普遍写像。
方針：アフィン被覆上の局所射を零核の検出射と分離性で貼り合わせる。
規約：KST §5、Stacks 080Y、基底の分離性・Noether 性は要求しない。
使われ方：可逆な中心を引き戻す射の基底上の因子化。
-/
def blowupUniversalLift : T ⟶ blowup I :=
  𝒰.openCover.glueMorphisms (blowupUniversalLocalLift I 𝒰 V φ b hreg hI) (fun i j => by
    have := blowupπ_restrict_complement_isIso I
    refine local_lift_overlap_hom_ext (blowupπ I) (centerComplement I) (𝒰.f i) (𝒰.f j)
      (blowupUniversalLocalLift I 𝒰 V φ b hreg hI i)
      (blowupUniversalLocalLift I 𝒰 V φ b hreg hI j) ?_
      (Spec.map (CommRingCat.ofHom
        (algebraMap (𝒰.X i) (Localization.Away (b i))))) ?_ ?_
    · simp only [Category.assoc, blowupUniversalLocalLift_base I f 𝒰 V φ b hreg hI hbase]
      exact pullback.condition_assoc _
    · exact specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
        (Localization.Away (b i)) (Submonoid.powers_le.mpr (hreg i)))
    · rw [blowupUniversalLocalLift_base I f 𝒰 V φ b hreg hI hbase]
      exact blowupUniversal_detector_range I f 𝒰 V φ b hI hbase i)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の基底上の普遍写像は指定された基底射を因子化する。
方針：始域のアフィン開被覆で局所交換式を使う。
規約：KST §5、Stacks 080Y、blowup の構造射との等式。
使われ方：可逆中心による実際の支配射の構成。
-/
@[reassoc] theorem blowupUniversalLift_base :
    blowupUniversalLift I f 𝒰 V φ b hreg hI hbase ≫ blowupπ I = f := by
  apply 𝒰.openCover.hom_ext
  intro i
  simp only [blowupUniversalLift, Scheme.Cover.ι_glueMorphisms_assoc,
    blowupUniversalLocalLift_base I f 𝒰 V φ b hreg hI hbase]
  rfl

include hreg

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心の逆像が局所的に正則単項となる始域からの一般 blowup への射は基底上で一意。
方針：各アフィン被覆上で正則生成元を局所化し、零核と中心外同型で一致を検出する。
規約：KST §5、Stacks 080Y、被約性や Noether 性は要求しない。
使われ方：一般基底上の普遍写像の一意性と選択への非依存性。
-/
theorem blowupUniversal_hom_ext {g h : T ⟶ blowup I}
    (hg : g ≫ blowupπ I = f) (hh : h ≫ blowupπ I = f) : g = h := by
  apply 𝒰.openCover.hom_ext
  intro i
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (𝒰.X i) (Localization.Away (b i))))
  apply hom_ext_of_ker_eq_bot_of_separated (blowupπ I)
    (by simp only [Category.assoc, hg, hh]) q
    (specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
      (Localization.Away (b i)) (Submonoid.powers_le.mpr (hreg i))))
  have := blowupπ_restrict_complement_isIso I
  apply hom_ext_of_isIso_restrict (blowupπ I) (centerComplement I)
  · simp only [Category.assoc, hg, hh]
  · simp only [Category.assoc, hg]
    exact blowupUniversal_detector_range I f 𝒰 V φ b hI hbase i

/--
概要：局所的に正則単項な像中心の条件の下で、一般 blowup への持ち上げはただ一つ存在する。
方針：実際に貼り合わせた持ち上げとその基底上の一意性を束ねる。
規約：KST §5、Stacks 080Y、仮定は局所環準同型と像イデアルの等式のみ。
使われ方：通常 blowup の幾何学的普遍性。
-/
theorem existsUnique_blowup_universal_lift :
    ∃! g : T ⟶ blowup I, g ≫ blowupπ I = f := by
  refine ⟨blowupUniversalLift I f 𝒰 V φ b hreg hI hbase,
    blowupUniversalLift_base I f 𝒰 V φ b hreg hI hbase, ?_⟩
  intro g hg
  exact blowupUniversal_hom_ext I f 𝒰 V φ b hreg hI hbase hg
    (blowupUniversalLift_base I f 𝒰 V φ b hreg hI hbase)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
