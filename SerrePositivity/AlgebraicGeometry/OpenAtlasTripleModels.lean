module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasModelProperties
public import SerrePositivity.AlgebraicGeometry.CartesianPullbackComparison

/-!
概要：元の三重交叉と模型の三重交叉の実際の Cartesian な比較。
方針：二重交叉の二つの Cartesian な比較のファイバー積を取り、基底への比較と合成する。
規約：元の環の Noether 性を要求しない。模型の有限表示性は係数側で供給する。
使われ方：G2 の三重交叉の射を固定した有限表示の模型へ降ろす。
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

/-- 元の三重交叉から模型の三重交叉への実際の比較射。 -/
def tripleComparison (i a b : I) :
    pullback (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ⟶
      pullback (m.overlap i a).ι (m.overlap i b).ι :=
  cartesianPullbackMap (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b))
    (m.overlap i a).ι (m.overlap i b).ι (m.comparison i)
    (m.overlapComparison i a) (m.overlapComparison i b)
    (m.isPullback_overlapComparison i a) (m.isPullback_overlapComparison i b)

/-- 三重交叉の比較も元のチャートの比較の底変換。 -/
theorem isPullback_tripleComparison (i a b : I) :
    IsPullback (m.tripleComparison i a b)
      (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫ pullback.fst (j i) (j a))
      (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫ (m.overlap i a).ι) (m.comparison i) :=
  isPullback_cartesianPullbackMap _ _ _ _ _ _ _
    (m.isPullback_overlapComparison i a) (m.isPullback_overlapComparison i b)

/-- 三重交叉の比較は係数基底上でも Cartesian。 -/
theorem isPullback_tripleComparison_toBase (i a b : I) :
    IsPullback (m.tripleComparison i a b)
      (pullback.fst (pullback.fst (j i) (j a)) (pullback.fst (j i) (j b)) ≫
        pullback.fst (j i) (j a) ≫ j i ≫ f)
      (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫ (m.overlap i a).ι ≫ m.map i)
      (Spec.map (CommRingCat.ofHom (algebraMap m.A R))) := by
  simpa only [Category.assoc] using (m.isPullback_tripleComparison i a b).paste_vert (m.cartesian i)

/-- 模型の三重交叉は係数基底上 qcqs な局所有限表示対象。 -/
theorem finitePresentation_triple [IsNoetherianRing k] (i a b : I) :
    LocallyOfFinitePresentation
        (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫ (m.overlap i a).ι ≫ m.map i) ∧
      QuasiCompact (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫
        (m.overlap i a).ι ≫ m.map i) ∧
      QuasiSeparated (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫
        (m.overlap i a).ι ≫ m.map i) := by
  letI : IsNoetherian (m.obj i) := m.isNoetherian_obj i
  letI : LocallyOfFinitePresentation (m.map i) := m.fp i
  letI : QuasiCompact (m.map i) := m.qc i
  letI : QuasiSeparated (m.map i) := m.qs i
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
