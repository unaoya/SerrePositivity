module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
public import SerrePositivity.AlgebraicGeometry.OpenModelComparison
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：実際に選んだアトラス模型の重なりの有限表示性と Cartesian 比較。
方針：有限生成係数環上の有限型性で Noether 性を供給し、開の比較と合成を使う。
規約：元の環 R に Noether 性を要求しない。
使われ方：G2 の重なりの遷移・逆・三重交叉の射の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)

/-- 係数環の Noether 性は、指定係数環 k と有限生成性から供給する。 -/
theorem isNoetherian_coefficients [IsNoetherianRing k] : IsNoetherianRing m.A :=
  isNoetherianRing_of_fg m.fg

/-- 模型の各チャートは、元の環 R の Noether 性を使わず Noether となる。 -/
theorem isNoetherian_obj [IsNoetherianRing k] (i : I) : IsNoetherian (m.obj i) := by
  letI : IsNoetherianRing m.A := m.isNoetherian_coefficients
  letI : IsAffine (m.obj i) := m.affine i
  letI : LocallyOfFinitePresentation (m.map i) := m.fp i
  letI : IsLocallyNoetherian (m.obj i) := LocallyOfFiniteType.isLocallyNoetherian (m.map i)
  exact {}

/-- 元の二重交叉から模型の重なりへの実際の比較射。 -/
def overlapComparison (i a : I) : pullback (j i) (j a) ⟶ m.overlap i a :=
  openModelComparison (pullback.fst (j i) (j a)) (m.comparison i) (m.overlap i a)
    ((m.overlap_eq i a).trans (Scheme.Hom.opensRange_pullbackFst (j a) (j i)).symm)

/-- 元の二重交叉と模型の重なりの比較は Cartesian。 -/
theorem isPullback_overlapComparison (i a : I) :
    IsPullback (m.overlapComparison i a) (pullback.fst (j i) (j a))
      (m.overlap i a).ι (m.comparison i) :=
  isPullback_openModelComparison _ _ _ _

/-- 重なりの比較も、同じ係数基底上の実際の Cartesian 比較。 -/
theorem isPullback_overlapComparison_toBase (i a : I) :
    IsPullback (m.overlapComparison i a) (pullback.fst (j i) (j a) ≫ j i ≫ f)
      ((m.overlap i a).ι ≫ m.map i) (Spec.map (CommRingCat.ofHom (algebraMap m.A R))) := by
  simpa only [Category.assoc] using (m.isPullback_overlapComparison i a).paste_vert (m.cartesian i)

/-- 全重なりの模型は、係数基底上 qcqs な局所有限表示対象。 -/
theorem finitePresentation_overlap [IsNoetherianRing k] (i a : I) :
    LocallyOfFinitePresentation ((m.overlap i a).ι ≫ m.map i) ∧
      QuasiCompact ((m.overlap i a).ι ≫ m.map i) ∧ QuasiSeparated ((m.overlap i a).ι ≫ m.map i) := by
  letI : IsNoetherian (m.obj i) := m.isNoetherian_obj i
  letI : LocallyOfFinitePresentation (m.map i) := m.fp i
  letI : QuasiCompact (m.map i) := m.qc i
  letI : QuasiSeparated (m.map i) := m.qs i
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
