module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorVanishing
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel

/-!
# perfectoid 化の核の BS 著者版 Lemma 10.3（BS 著者版 Lemma 10.3）

## 概要
perfectoid 環の完備導来テンソル積は離散で perfectoid、核と商の完備導来テンソルは零、単項商の perfectoid 化の核についての BS 著者版 Lemma 10.3。
商の自己積の証明に、perfectoid 環どうしの完備導来テンソルの離散性と perfectoid 性を使う。

## 方針
Tor 独立性を平坦な全射表示で示す（BS 著者版 Lemma 10.3 の単体的証明に対する古典的な代数計算）。

## 規約
—

## 使われ方
BS 著者版 Proposition 10.2・BS 著者版 Remark 10.7、CLMST。
-/

universe u

/-! ## BS 著者版 Lemma 10.3 の核と商の混合積

## 概要
perfectoid 環の perfectoid 商について、核と商の完備導来テンソルは零である。
## 方針
商の自己積の同型性と単位則から、短完全列の第二射が同型と示す。
## 規約
実テンソル・標準射を使う。核に有限性・通常の平坦性は仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の核の自己積に接続する。
-/

@[expose] public noncomputable section Lemma103KernelTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

private lemma Almost.quotient_tensor_map_mul (I : Ideal R) :
    (_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).map
        (ModuleCat.ofHom I.mkQ) ≫
      (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom =
    (_root_.SerrePositivity.boundedAboveDerivedTensorRightUnitor
      (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I)))).hom.hom := by
  let Q := ModuleCat.of R (R ⧸ I)
  let q : ModuleCat.of R R ⟶ Q := ModuleCat.ofHom I.mkQ
  have he : (tensorLeft Q).map q ≫ ModuleCat.ofHom (LinearMap.mul' R (R ⧸ I)) =
      (ρ_ Q).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x r
    change x * (Ideal.Quotient.mk I r) = r • x
    rw [Algebra.smul_def, mul_comm]
    rfl
  change (_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor Q).map q ≫
    ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation Q).app Q ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R (R ⧸ I)))) = _
  rw [← Category.assoc, (_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation Q).naturality q]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, he]
  exact _root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation_rightUnitor Q

/--
## 概要
perfectoid 環 R の perfectoid 商 R/I と核 I の完備導来テンソルは零である（BS 著者版 Lemma 10.3 の混合積消滅で任意の perfectoid 商の場合）。
## 方針
商の実自己積が同型であることと標準単位則により、I→R→R/I の完備テンソル三角形の
第二射が同型になるため、第一対象は零となる。
## 規約
p ねじれ・零環を許す。通常の自己 Tor の消滅は仮定しない。
## 使われ方
perfectoid 化の核へ特殊化し、核の自己積と almost 拡大閉性の証明に使う。
-/
theorem Almost.integralPerfectoid_completedQuotientTensorIdeal_isZero
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ I) p) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R (R ⧸ I))).obj
        (ModuleCat.of R I))) := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  apply completedTensor_isZero_of_shortExact_rightMap_isIso (p : R)
    (ModuleCat.of R (R ⧸ I)) S hS
  let F := derivedComplexCompletionFunctor R (p : R)
  have : IsIso (F.map (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) :=
    _root_.SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso p R I hR hQ
  have he := congrArg F.map (_root_.SerrePositivity.BhattScholze.Almost.quotient_tensor_map_mul I)
  rw [Functor.map_comp] at he
  have : IsIso (F.map ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor
      (ModuleCat.of R (R ⧸ I))).map (ModuleCat.ofHom I.mkQ)) ≫
      F.map (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (F.map (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)).hom)

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
theorem Almost.integralPerfectoid_completedIdealTensorQuotient_isZero
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ I) p) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj
        (ModuleCat.of R (R ⧸ I)))) := by
  let e := (DerivedCategory.Minus.ι (C := ModuleCat R)).mapIso
    (_root_.SerrePositivity.boundedAboveDerivedTensorSymmetry
      (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I))
      (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I))))
  exact (_root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedQuotientTensorIdeal_isZero p I hR hQ).of_iso
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
def Almost.boundedAboveDerivedIdealMul (I : Ideal R) :
    _root_.SerrePositivity.boundedAboveDerivedTensor.obj
      (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I),
        _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I)) ⟶
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I) :=
  ObjectProperty.homMk
    ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R I)).app
      (ModuleCat.of R I) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R I)))

private lemma Almost.ideal_tensor_subtype_mul (I : Ideal R) :
    (_root_.SerrePositivity.BhattScholze.Almost.boundedAboveDerivedIdealMul I).hom =
      (_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).map
          (ModuleCat.ofHom I.subtype) ≫
        (_root_.SerrePositivity.boundedAboveDerivedTensorRightUnitor
          (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I))).hom.hom := by
  let M := ModuleCat.of R I
  have he : (tensorLeft M).map (ModuleCat.ofHom I.subtype) ≫ (ρ_ M).hom =
      ModuleCat.ofHom (LinearMap.mul' R I) := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    apply Subtype.ext
    change (y : R) * (x : R) = (x : R) * (y : R)
    exact mul_comm _ _
  rw [← _root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation_rightUnitor]
  rw [← Category.assoc,
    (_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation M).naturality (ModuleCat.ofHom I.subtype)]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f => (_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation M).app M ≫
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
perfectoid 化の核に特殊化して BS 著者版 Lemma 10.3 の第一主張を与える。
-/
theorem Almost.integralPerfectoid_completedIdealMul_isIso
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (_root_.SerrePositivity.BhattScholze.Almost.boundedAboveDerivedIdealMul I).hom) := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  have : IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).map
        (ModuleCat.ofHom I.subtype))) :=
    completedTensor_shortExact_leftMap_isIso_of_isZero (p : R) (ModuleCat.of R I) S hS
      (_root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealTensorQuotient_isZero p I hR hQ)
  rw [_root_.SerrePositivity.BhattScholze.Almost.ideal_tensor_subtype_mul, Functor.map_comp]
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
theorem Almost.integralPerfectoid_quotientIdeal_isModuleComplete
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ I) p) :
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
def Almost.completedDerivedIdealMul (a : R) (I : Ideal R)
    (hI : IsModuleComplete R a (ModuleCat.of R I)) :
    (derivedComplexCompletionFunctor R a).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj (ModuleCat.of R I)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R I) :=
  (derivedComplexCompletionFunctor R a).map (_root_.SerrePositivity.BhattScholze.Almost.boundedAboveDerivedIdealMul I).hom ≫
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
theorem Almost.integralPerfectoid_completedDerivedIdealMul_isIso
    (p : ℕ) [Fact p.Prime] (I : Ideal R)
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hQ : _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ I) p) :
    IsIso (_root_.SerrePositivity.BhattScholze.Almost.completedDerivedIdealMul (p : R) I
      (_root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_quotientIdeal_isModuleComplete p I hR hQ)) := by
  have := _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealMul_isIso p I hR hQ
  unfold _root_.SerrePositivity.BhattScholze.Almost.completedDerivedIdealMul
  infer_instance

end SerrePositivity.BhattScholze

end Lemma103KernelTensor

/-! ## BS 著者版 Lemma 10.3 の一般の perfectoid テンソル

## 概要
BS 著者版 Lemma 10.3 の証明中の主張（印刷 pp.78–79）を、実際の完備導来テンソルの
全非零次数のホモロジー消滅と、その実 H⁰ 環の perfectoid 性として公開する。

## 方針
既存の Fontaine 環・完全 prism・二段階完備化による証明を再利用する。
完全標数 p 環の Tor 独立性は証明済みであり、追加仮定にはしない。

## 規約
G2 の元の完備導来テンソルと `derivedH0CommRing` を使う。零環と p ねじれを許す。

## 使われ方
BS 著者版 Lemma 10.3 の商環の自己テンソルと、perfectoid イデアルの依存監査の入口である。
-/

@[expose] public noncomputable section Lemma103PerfectoidTensor

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/--
## 概要
perfectoid 環 R 上の perfectoid 代数 S,T の完備導来テンソルは全非零次数で
ホモロジーが零であり、同じ対象の実 H⁰ 環は perfectoid である。

## 方針
既存の完全 prism による次数零集中と perfectoid 性を使い、標準 t 構造の
判定から非零次数の消滅を取り出す。

## 規約
有限性・平坦性・p 正則性・非零性を仮定しない。H⁰ の環構造を明示する。

## 使われ方
S=T=R/K に特殊化して 商環の自己積に用いる。
-/
theorem Almost.lemma103_perfectoidTensor
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hS : _root_.SerrePositivity.IsIntegralPerfectoid S p)
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) :
    let X := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := _root_.SerrePositivity.derivedH0CommRing X
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.X.obj)) ∧
      _root_.SerrePositivity.IsIntegralPerfectoid
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.X.obj) p := by
  obtain ⟨hpure, hperf⟩ := _root_.SerrePositivity.BhattScholze.integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT
  refine ⟨?_, hperf⟩
  intro i hi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · exact (DerivedCategory.isGE_iff _ 0).mp hpure.1 i hneg
  · exact (DerivedCategory.isLE_iff _ 0).mp hpure.2 i hpos

end SerrePositivity.BhattScholze

end Lemma103PerfectoidTensor

/-! ## 単項商の perfectoid 化の核に対する BS 著者版 Lemma 10.3

## 概要
B3 の選ばれた perfectoid 化の核について、BS 著者版 Lemma 10.3（印刷 pp.78–79）を述べる。
## 方針
B4 の一般全射性により商を元の perfectoid 化へ同定し、一般 perfectoid 商の結果を適用する。
## 規約
既存の perfectoidIdeal と IsPerfectoidization を使い、p ねじれなしを仮定しない。
## 使われ方
BS 著者版 Remark 10.7 の mod p 冪冪等性と BS 著者版 Proposition 10.2 の拡大閉性の入口である。
-/

@[expose] public noncomputable section PerfectoidIdealLemma103

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核で割った R/K は perfectoid 環である。
## 方針
B4 の一般全射性と既存の核商同型により、B3 の選ばれた perfectoid 化に移す。
## 規約
単項商の導来完備性を使い、p ねじれなしを仮定しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の商の実積の標的の完備性を供給する。
-/
theorem Almost.perfectoidIdeal_quotient_isIntegralPerfectoid :
    _root_.SerrePositivity.IsIntegralPerfectoid (R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) p := by
  let f := _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R (Ideal.span {g}) p hR
  have hf := _root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  have hs : Function.Surjective f :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
      (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective
      (isModuleComplete_principal_quotient_natCast R p g (hR.isModuleComplete R p)) f hf
  let e : R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g ≃+*
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R (Ideal.span {g}) p hR :=
    RingHom.quotientKerEquivOfSurjective (hs.comp Ideal.Quotient.mk_surjective)
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p e.symm hf.1

/--
## 概要
単項商の perfectoid 化の核 K は導来 p 完備である。
## 方針
B4 の全射性による perfectoid 商表示に、一般の核の完備性を適用する。
## 規約
K は既存の perfectoidIdeal そのものである。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の第一射の標的を固定する。
-/
theorem Almost.perfectoidIdeal_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g)) :=
  _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_quotientIdeal_isModuleComplete p (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hR
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

/--
## 概要
K を単項商の perfectoid 化の核とすると、実積 K⊗̂ᴸK→K と
(R/K)⊗̂ᴸ(R/K)→(R/K) の完備化は同型であり、K⊗̂ᴸ(R/K) は零である（BS 著者版 Lemma 10.3 の三つの主張で単項 J の場合）。
## 方針
B4 による同じ核の perfectoid 商表示に、一般商の三角形による三主張を適用する。
## 規約
第一射は元の K[0] を標的とする標準積。第二射の標的の完備化は
perfectoid 商の導来完備性で元の商に標準同定される。p 正則性は追加しない。
## 使われ方
BS 著者版 Remark 10.7 と BS 著者版 Proposition 10.2 の核イデアルに関する結果を供給する。
-/
theorem Almost.perfectoidIdeal_lemma103 :
    let K := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
    IsIso (_root_.SerrePositivity.BhattScholze.Almost.completedDerivedIdealMul (p : R) K
      (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isModuleComplete R p hR g)) ∧
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ K)).hom) ∧
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R K)).obj
        (ModuleCat.of R (R ⧸ K)))) := by
  have hQ := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g
  exact ⟨_root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso p _ hR hQ,
    _root_.SerrePositivity.BhattScholze.integralPerfectoid_completedQuotientMul_isIso p R _ hR hQ,
    _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealTensorQuotient_isZero p _ hR hQ⟩

/--
## 概要
商の実完備導来自己テンソルから、元の商 (R/K)[0] への標準積を定義する。
## 方針
元の導来積の完備化に、perfectoid 商の標準完備化単位の逆を合成する。
## 規約
K は perfectoidIdeal であり、標的の別コピーへの抽象的同型で代用しない。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の第二射を元の商を標的として渡す。
-/
def Almost.perfectoidIdeal_completedQuotientMul :
    let Q := R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
    (derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R Q)).obj (ModuleCat.of R Q)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R Q) :=
  (derivedComplexCompletionFunctor R (p : R)).map
      (_root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g)).hom ≫
    (derivedComplexCompletionUnitIso R (p : R) _
      ((_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g).isModuleComplete_algebra R _ p)).inv

/--
## 概要
元の商を標的とする実積 (R/K)⊗̂ᴸ(R/K)→(R/K)[0] は同型である（BS 著者版 Lemma 10.3 の第二の積射で単項 J の場合）。
## 方針
BS 著者版 Lemma 10.3 の第二主張と、標的の perfectoid 性による標準単位同型を合成する。
## 規約
完備化単位によって定義した同じ積について主張する。
## 使われ方
BS 著者版 Lemma 10.3（印刷 pp.78–79）の元の商を標的とする第二主張である。
-/
theorem Almost.perfectoidIdeal_completedQuotientMul_isIso :
    IsIso (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedQuotientMul R p hR g) := by
  have := (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103 R p hR g).2.1
  unfold _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedQuotientMul
  infer_instance

end SerrePositivity.BhattScholze

end PerfectoidIdealLemma103

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedDerivedIdealMul_isIso
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealMul_isIso
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedIdealTensorQuotient_isZero
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.integralPerfectoid_completedQuotientTensorIdeal_isZero
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedQuotientMul_isIso
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103
