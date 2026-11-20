module

public import SerrePositivity.AlgebraicGeometry.AffineRegularLift
public import SerrePositivity.AlgebraicGeometry.RegularCenterCover

/-!
概要：KST §5 の正則な単項像中心に対するアフィン blowup の普遍写像。
方針：生成係数の基本開被覆上の局所射を、正則局所化と分離性で貼り合わせる。
規約：生成元は中心の元の像として大域的に選べなくてよい。
使われ方：一般の可逆な像中心の普遍性と admissible blowup の共通細分。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (b : S)
  (hreg : b ∈ nonZeroDivisors S) (hI : I.map f = Ideal.span {b})

/--
概要：正則な像中心の生成係数による実際のアフィン開被覆。
方針：係数の単位イデアル生成を標準の局所化被覆に渡す。
規約：KST §5、被覆対象は Spec S。
使われ方：正則単項中心からの局所普遍写像の貼り合わせ。
-/
def regularCenterCover : (Spec (.of S)).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop
    (fun s : regularCenterCoefficients I f b => s.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      span_regularCenterCoefficients I f b hreg hI)

/--
概要：一つの生成係数に対応する局所的な普遍写像。
方針：その係数を可逆化し、中心元の像が正則な生成元となる局所射を使う。
規約：KST §5、環準同型とスキーム射を実際に構成する。
使われ方：正則単項中心からの大域普遍写像の局所成分。
-/
def principalRegularLocalLift (s : regularCenterCoefficients I f b) :
    Spec (.of (Localization.Away s.1)) ⟶ affineBlowup I :=
  affineBlowupRegularLift I ((algebraMap S (Localization.Away s.1)).comp f)
    s.2.choose
    (regularCenter_localized_regular I f b hreg s.2.choose s.1 s.2.choose_spec)
    (regularCenter_localized_image I f b hI s.2.choose s.1 s.2.choose_spec)

set_option backward.isDefEq.respectTransparency false in
/--
概要：生成係数上の局所普遍写像は Spec S 上の基底射と両立する。
方針：正則チャート持ち上げの係数保存と Spec の反変性を使う。
規約：KST §5、被覆射との合成で述べる。
使われ方：局所射の重なり上の一致と貼り合わせ後の基底両立性。
-/
@[reassoc] theorem principalRegularLocalLift_base (s : regularCenterCoefficients I f b) :
    principalRegularLocalLift I f b hreg hI s ≫ affineBlowupπ I =
      (regularCenterCover I f b hreg hI).f s ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [principalRegularLocalLift, affineBlowupRegularLift_base]
  change Spec.map (CommRingCat.ofHom f ≫
    CommRingCat.ofHom (algebraMap S (Localization.Away s.1))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s.1))) ≫
      Spec.map (CommRingCat.ofHom f)
  exact Spec.map_comp _ _

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な単項像中心からのアフィン blowup への大域普遍写像。
方針：生成係数による基本開被覆上の局所持ち上げを一意性で貼り合わせる。
規約：KST §5、正則な生成元 b は f(a) である必要はない。
使われ方：可逆な中心を引き戻すスキームからの普遍写像。
-/
def affineBlowupPrincipalRegularLift : Spec (.of S) ⟶ affineBlowup I :=
  (regularCenterCover I f b hreg hI).openCover.glueMorphisms
    (principalRegularLocalLift I f b hreg hI) (fun s t => by
      apply affineBlowup_regular_overlap I
        ((algebraMap S (Localization.Away s.1)).comp f) s.2.choose
        (regularCenter_localized_regular I f b hreg s.2.choose s.1 s.2.choose_spec)
        ((regularCenterCover I f b hreg hI).f s)
        ((regularCenterCover I f b hreg hI).f t)
        (principalRegularLocalLift I f b hreg hI s)
        (principalRegularLocalLift I f b hreg hI t)
      · exact affineBlowupRegularLift_base ..
      · simp only [Category.assoc, principalRegularLocalLift_base]
        exact pullback.condition_assoc _)

set_option backward.isDefEq.respectTransparency false in
/--
概要：貼り合わせた正則単項中心からの普遍写像は指定された基底射を持つ。
方針：生成係数の開被覆で等式を検出する。
規約：KST §5、Spec R への実際の射の等式。
使われ方：共通細分の射の基底両立性。
-/
@[reassoc] theorem affineBlowupPrincipalRegularLift_base :
    affineBlowupPrincipalRegularLift I f b hreg hI ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom f) := by
  apply (regularCenterCover I f b hreg hI).openCover.hom_ext
  intro s
  simp only [affineBlowupPrincipalRegularLift, Scheme.Cover.ι_glueMorphisms_assoc]
  exact principalRegularLocalLift_base I f b hreg hI s

include b hreg hI

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な単項像中心を持つアフィンスキームからの blowup への射は基底上で一意。
方針：生成係数の基本開被覆で制限し、中心元の像が正則な場合に帰着する。
規約：KST §5、正則な生成元 b は中心元の像として選ばなくてよい。
使われ方：正則単項中心に対する普遍写像の一意性。
-/
theorem affineBlowup_hom_ext_of_principal_regular
    {g h : Spec (.of S) ⟶ affineBlowup I}
    (hg : g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f)) : g = h := by
  apply (regularCenterCover I f b hreg hI).openCover.hom_ext
  intro s
  apply affineBlowup_hom_ext_of_regular I
    ((algebraMap S (Localization.Away s.1)).comp f) s.2.choose
    (regularCenter_localized_regular I f b hreg s.2.choose s.1 s.2.choose_spec)
  · rw [Category.assoc, hg]
    exact (principalRegularLocalLift_base I f b hreg hI s).symm.trans
      (affineBlowupRegularLift_base ..)
  · rw [Category.assoc, hh]
    exact (principalRegularLocalLift_base I f b hreg hI s).symm.trans
      (affineBlowupRegularLift_base ..)

/--
概要：正則な単項像中心に対する blowup への基底上の持ち上げの存在と一意性。
方針：構成した大域普遍写像と正則単項中心の一意性を組み合わせる。
規約：KST §5、追加の Noether 性・有限生成性を仮定しない。
使われ方：局所的に可逆となる中心の普遍性のアフィン部分。
-/
theorem existsUnique_affineBlowup_lift_of_principal_regular :
    ∃! g : Spec (.of S) ⟶ affineBlowup I,
      g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f) := by
  refine ⟨affineBlowupPrincipalRegularLift I f b hreg hI,
    affineBlowupPrincipalRegularLift_base I f b hreg hI, ?_⟩
  intro g hg
  exact affineBlowup_hom_ext_of_principal_regular I f b hreg hI hg
    (affineBlowupPrincipalRegularLift_base I f b hreg hI)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
