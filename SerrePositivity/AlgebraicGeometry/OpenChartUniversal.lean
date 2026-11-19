module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BlowupAffineOpenMap
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.PrincipalRegularLift
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：KST §5、Stacks 080Y の任意のアフィン開チャートによる blowup の普遍写像。
方針：与えられたチャート環の正則単項中心から局所射を作り、零核の中心外検出で貼り合わせる。
規約：標準的な切断環の Spec にチャート環を同一視しない。
使われ方：積中心のチャートから blowup の合成への支配射を構成する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X T : Scheme.{u}} (K : X.IdealSheafData) (f : T ⟶ X)
  (𝒰 : T.AffineOpenCover) (A : 𝒰.I₀ → CommRingCat.{u})
  (j : ∀ i, Spec (A i) ⟶ X) (hj : ∀ i, IsOpenImmersion (j i))
  (φ : ∀ i, A i ⟶ 𝒰.X i) (b : ∀ i, 𝒰.X i)
  (hreg : ∀ i, b i ∈ nonZeroDivisors (𝒰.X i))
  (hK : ∀ i, (specIdealEquiv (A i) (K.comap (j i))).map (φ i).hom = Ideal.span {b i})
  (hbase : ∀ i, Spec.map (φ i) ≫ j i = 𝒰.f i ≫ f)

/--
概要：任意のアフィン開チャート上の正則単項中心からの局所普遍写像。
方針：環の持ち上げと開チャートの blowup 比較射を合成する。
規約：KST §5、Stacks 080Y、基底への局所射を保持する。
使われ方：一般のチャート表示での大域普遍写像の局所成分。
-/
def openChartUniversalLocalLift (i : 𝒰.I₀) : Spec (𝒰.X i) ⟶ blowup K := by
  have := hj i
  exact affineBlowupPrincipalRegularLift (specIdealEquiv (A i) (K.comap (j i)))
    (φ i).hom (b i) (hreg i) (hK i) ≫ blowupAffineOpenMap (j i) K

include hbase

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の開チャートによる局所普遍写像は指定された基底射と両立する。
方針：環の持ち上げと開チャート比較射の二つの構造射公式を使う。
規約：KST §5、Stacks 080Y、実際の X 上の射。
使われ方：局所射の重なり上の一致。
-/
@[reassoc] theorem openChartUniversalLocalLift_base (i : 𝒰.I₀) :
    openChartUniversalLocalLift K 𝒰 A j hj φ b hreg hK i ≫ blowupπ K = 𝒰.f i ≫ f := by
  have := hj i
  unfold openChartUniversalLocalLift
  rw [Category.assoc, blowupAffineOpenMap_base, ← Category.assoc,
    affineBlowupPrincipalRegularLift_base]
  exact hbase i

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の開チャートの正則単項像中心の条件からの実際の大域普遍写像。
方針：局所射を正則生成元の局所化による零核の検出射で貼り合わせる。
規約：KST §5、Stacks 080Y、始域・基底の Noether 性や分離性は要求しない。
使われ方：積中心による blowup の合成の支配。
-/
def openChartUniversalLift : T ⟶ blowup K :=
  𝒰.openCover.glueMorphisms (openChartUniversalLocalLift K 𝒰 A j hj φ b hreg hK) (fun i k => by
    have := blowupπ_restrict_complement_isIso K
    refine local_lift_overlap_hom_ext (blowupπ K) (centerComplement K) (𝒰.f i) (𝒰.f k)
      (openChartUniversalLocalLift K 𝒰 A j hj φ b hreg hK i)
      (openChartUniversalLocalLift K 𝒰 A j hj φ b hreg hK k) ?_
      (Spec.map (CommRingCat.ofHom
        (algebraMap (𝒰.X i) (Localization.Away (b i))))) ?_ ?_
    · simp only [Category.assoc, openChartUniversalLocalLift_base K f 𝒰 A j hj φ b hreg hK hbase]
      exact pullback.condition_assoc _
    · exact specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
        (Localization.Away (b i)) (Submonoid.powers_le.mpr (hreg i)))
    · rw [openChartUniversalLocalLift_base K f 𝒰 A j hj φ b hreg hK hbase, ← hbase i]
      exact local_principalDetector_range K (j i) (φ i) (b i)
        ((hK i).symm ▸ Ideal.subset_span (Set.mem_singleton (b i))))

set_option backward.isDefEq.respectTransparency false in
/--
概要：任意の開チャートで貼り合わせた普遍写像は指定された基底射を因子化する。
方針：始域のアフィン開被覆上で局所構造射公式を使う。
規約：KST §5、Stacks 080Y、基底 X への射の等式。
使われ方：合成の支配射の可換三角形。
-/
@[reassoc] theorem openChartUniversalLift_base :
    openChartUniversalLift K f 𝒰 A j hj φ b hreg hK hbase ≫ blowupπ K = f := by
  apply 𝒰.openCover.hom_ext
  intro i
  simp only [openChartUniversalLift, Scheme.Cover.ι_glueMorphisms_assoc,
    openChartUniversalLocalLift_base K f 𝒰 A j hj φ b hreg hK hbase]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
