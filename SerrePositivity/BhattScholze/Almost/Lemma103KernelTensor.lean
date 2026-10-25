module

public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedQuotientMul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorShortExact
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure

/-!
# Lemma 10.3 の核と商の混合積
## 概要
perfectoid 環の perfectoid 商について、核と商の完備導来テンソルは零である。
## 方針
商の自己積の同型性と単位則から、短完全列の第二射が同型と示す。
## 規約
実テンソル・標準射を使う。核に有限性・通常の平坦性は仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の核の自己積に接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits MonoidalCategory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

private lemma quotient_tensor_map_mul (I : Ideal R) :
    (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).map
        (ModuleCat.ofHom I.mkQ) ≫
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom =
    (boundedAboveDerivedTensorRightUnitor
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I)))).hom.hom := by
  let Q := ModuleCat.of R (R ⧸ I)
  let q : ModuleCat.of R R ⟶ Q := ModuleCat.ofHom I.mkQ
  have he : (tensorLeft Q).map q ≫ ModuleCat.ofHom (LinearMap.mul' R (R ⧸ I)) =
      (ρ_ Q).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x r
    change x * (Ideal.Quotient.mk I r) = r • x
    rw [Algebra.smul_def, mul_comm]
    rfl
  change (boundedAboveDerivedTensorModuleFunctor Q).map q ≫
    ((boundedAboveDerivedTensorModuleAugmentation Q).app Q ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R (R ⧸ I)))) = _
  rw [← Category.assoc, (boundedAboveDerivedTensorModuleAugmentation Q).naturality q]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, he]
  exact boundedAboveDerivedTensorModuleAugmentation_rightUnitor Q

/--
## 概要
perfectoid 環 R の perfectoid 商 R/I と核 I の完備導来テンソルは零である
（BS 著者版 Lemma 10.3、印刷 pp.78–79）。
## 方針
商の実自己積が同型であることと標準単位則により、I→R→R/I の完備テンソル三角形の
第二射が同型になるため、第一対象は零となる。
## 規約
p ねじれ・零環を許す。通常の自己 Tor の消滅は仮定しない。
## 使われ方
perfectoid 化の核へ特殊化し、核の自己積と almost 拡大閉性の証明に使う。
-/
theorem integralPerfectoid_completedQuotientTensorIdeal_isZero
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).obj
        (ModuleCat.of R I))) := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  apply completedTensor_isZero_of_shortExact_rightMap_isIso (p : R)
    (ModuleCat.of R (R ⧸ I)) S hS
  let F := derivedComplexCompletionFunctor R (p : R)
  have : IsIso (F.map (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) :=
    integralPerfectoid_completedQuotientMul_isIso p R I hR hQ
  have he := congrArg F.map (quotient_tensor_map_mul I)
  rw [Functor.map_comp] at he
  have : IsIso (F.map ((boundedAboveDerivedTensorModuleFunctor
      (ModuleCat.of R (R ⧸ I))).map (ModuleCat.ofHom I.mkQ)) ≫
      F.map (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (F.map (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)

/--
## 概要
核 I と perfectoid 商 R/I の完備導来テンソルは零である
（BS 著者版 Lemma 10.3、印刷 pp.78–79）。
## 方針
商を左に置く既証の消滅を、元の導来テンソルの対称同型で移す。
## 規約
G2 の同じ完備化関手を用い、p 正則性を仮定しない。
## 使われ方
核の短完全列に I をテンソルし、その自己積の同型性を導く。
-/
theorem integralPerfectoid_completedIdealTensorQuotient_isZero
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj
        (ModuleCat.of R (R ⧸ I)))) := by
  let e := (DerivedCategory.Minus.ι (C := ModuleCat R)).mapIso
    (boundedAboveDerivedTensorSymmetry
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I))
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I))))
  exact (integralPerfectoid_completedQuotientTensorIdeal_isZero p I hR hQ).of_iso
    ((derivedComplexCompletionFunctor R (p : R)).mapIso e)

/--
## 概要
イデアルの通常の積 I⊗I→I から誘導される元の導来積を定義する。
## 方針
既存の標準導来テンソル増大射と、非単位的環 I の双線形な積を合成する。
## 規約
完備化は定義に含めず、元の射を保持する。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の実自己積を明示する。
-/
def boundedAboveDerivedIdealMul (I : Ideal R) :
    boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I),
        boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I)) ⟶
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I) :=
  ObjectProperty.homMk
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R I)).app
      (ModuleCat.of R I) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R I)))

private lemma ideal_tensor_subtype_mul (I : Ideal R) :
    (boundedAboveDerivedIdealMul I).hom =
      (boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).map
          (ModuleCat.ofHom I.subtype) ≫
        (boundedAboveDerivedTensorRightUnitor
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I))).hom.hom := by
  let M := ModuleCat.of R I
  have he : (tensorLeft M).map (ModuleCat.ofHom I.subtype) ≫ (ρ_ M).hom =
      ModuleCat.ofHom (LinearMap.mul' R I) := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    apply Subtype.ext
    change (y : R) * (x : R) = (x : R) * (y : R)
    exact mul_comm _ _
  rw [← boundedAboveDerivedTensorModuleAugmentation_rightUnitor]
  rw [← Category.assoc,
    (boundedAboveDerivedTensorModuleAugmentation M).naturality (ModuleCat.ofHom I.subtype)]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f => (boundedAboveDerivedTensorModuleAugmentation M).app M ≫
    (DerivedCategory.singleFunctor (ModuleCat R) 0).map f) he.symm

/--
## 概要
perfectoid 環 R の perfectoid 商の核 I の実自己積 I⊗̂ᴸI→I は同型である
（BS 著者版 Lemma 10.3、印刷 pp.78–79）。
## 方針
I→R→R/I に I を完備導来テンソルした三角形の第三対象の消滅から第一射を同型とし、
標準右単位射との合成が元の積に等しいことを使う。
## 規約
結論は定義した元の積への完備化関手の適用であり、抽象的な同型の存在ではない。
## 使われ方
perfectoid 化の核に特殊化して Lemma 10.3 の第一主張を与える。
-/
theorem integralPerfectoid_completedIdealMul_isIso
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedIdealMul I).hom) := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  have : IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).map
        (ModuleCat.ofHom I.subtype))) :=
    completedTensor_shortExact_leftMap_isIso_of_isZero (p : R) (ModuleCat.of R I) S hS
      (integralPerfectoid_completedIdealTensorQuotient_isZero p I hR hQ)
  rw [ideal_tensor_subtype_mul, Functor.map_comp]
  infer_instance

/--
## 概要
perfectoid 環の perfectoid 商の核は導来 p 完備である。
## 方針
両環の既証の導来完備性と、完備加群間の線形写像の核の完備性を使う。
## 規約
古典的完備性との同一視や p ねじれなしを仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の自己積の標的を元の核に同定する。
-/
theorem integralPerfectoid_quotientIdeal_isModuleComplete
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsModuleComplete R (p : R) (ModuleCat.of R I) := by
  have hc := isModuleComplete_ker R (p : R)
    (M := ModuleCat.of R R) (N := ModuleCat.of R (R ⧸ I)) I.mkQ
    (hR.isModuleComplete R p) (hQ.isModuleComplete_algebra R (R ⧸ I) p)
  change IsModuleComplete R (p : R) (ModuleCat.of R (LinearMap.ker I.mkQ)) at hc
  rw [Submodule.ker_mkQ] at hc
  exact hc

/--
## 概要
導来完備なイデアルの実完備導来自己テンソルから、元のイデアルへの標準積である。
## 方針
元の導来積を完備化し、標的の完備化単位の逆射を合成する。
## 規約
標的は完備化のコピーではなく元の I[0] であり、比較は標準単位で固定する。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の第一射を表す。
-/
def completedDerivedIdealMul (a : R) (I : Ideal R)
    (hI : IsModuleComplete R a (ModuleCat.of R I)) :
    (derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj (ModuleCat.of R I)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R I) :=
  (derivedComplexCompletionFunctor R a).map (boundedAboveDerivedIdealMul I).hom ≫
    (derivedComplexCompletionUnitIso R a _ hI).inv

/--
## 概要
perfectoid 商の核の標準積 I⊗̂ᴸI→I[0] は同型である。
## 方針
元の積の完備化の同型性と、核の導来完備性による標準単位同型を合成する。
## 規約
環と核の元の加群構造を保持する。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）を完備化されていない標的へ渡す。
-/
theorem integralPerfectoid_completedDerivedIdealMul_isIso
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : IsIntegralPerfectoid R p) (hQ : IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso (completedDerivedIdealMul (p : R) I
      (integralPerfectoid_quotientIdeal_isModuleComplete p I hR hQ)) := by
  have := integralPerfectoid_completedIdealMul_isIso p I hR hQ
  unfold completedDerivedIdealMul
  infer_instance

end SerrePositivity.BhattScholze
