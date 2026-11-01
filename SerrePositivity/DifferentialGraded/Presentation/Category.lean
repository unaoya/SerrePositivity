module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedTransport
public import SerrePositivity.DifferentialGraded.Category.HomTransport
public import SerrePositivity.DifferentialGraded.Category.Induced
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Presentation.Category

## 概要
9 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ComplexCode（旧 SerrePositivity/DifferentialGraded/Presentation/ComplexCode.lean） -/

/-!
概要：固定した自由加群の商で各次数を表示する複体の小さいコード型を与える。
方針：関係部分加群と商上の微分を保持し、既存の CochainComplex.of で評価する。
規約：任意の Type u の台をフィールドに持たず、固定基底上の関係だけを動かす。
使われ方：16時間試作で、出発 dg 圏の提示ラベル自体を Type u に保つ基盤。
-/

@[expose] public section ComplexCode
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (B : Type u)

structure DGComplexPresentationCode where
  relations : ℤ → Submodule R (B →₀ R)
  differential : ∀ n : ℤ, ModuleCat.of R ((B →₀ R) ⧸ relations n) ⟶
    ModuleCat.of R ((B →₀ R) ⧸ relations (n + 1))
  square : ∀ n, differential n ≫ differential (n + 1) = 0

namespace DGComplexPresentationCode

def value (c : DGComplexPresentationCode R B) : Complex R :=
  CochainComplex.of (fun n => ModuleCat.of R ((B →₀ R) ⧸ c.relations n))
    c.differential c.square

lemma small : Small.{u} (DGComplexPresentationCode R B) := inferInstance

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded
end

end ComplexCode

/-! ## ComplexFromSurjections（旧 SerrePositivity/DifferentialGraded/Presentation/ComplexFromSurjections.lean） -/

/-!
概要：固定自由加群から各次数への全射を持つ複体を、関係と微分の小さいコードへ戻す。
方針：各次数の核による商の同型で微分を共役し、同じ全次数の複体同型を構成する。
規約：各次数の生成元被覆は入力に保持し、任意の複体が κ で生成されるとは主張しない。
使われ方：c′ の係数閉包を出発 dg 圏の固定基底 Hom 提示へ符号化する準備。
-/

@[expose] public section ComplexFromSurjections
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R] (B : Type u) (X : Complex R)
  (q : ∀ n : ℤ, (B →₀ R) →ₗ[R] X.X n) (hq : ∀ n, Function.Surjective (q n))

namespace DGComplexPresentationCode

def quotientComponentIso (n : ℤ) :
    ModuleCat.of R ((B →₀ R) ⧸ LinearMap.ker (q n)) ≅ X.X n :=
  ((q n).quotKerEquivOfSurjective (hq n)).toModuleIso

def ofSurjections : DGComplexPresentationCode R B where
  relations n := LinearMap.ker (q n)
  differential n := (quotientComponentIso R B X q hq n).hom ≫ X.d n (n + 1) ≫
    (quotientComponentIso R B X q hq (n + 1)).inv
  square n := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (X.d n (n + 1)), X.d_comp_d, zero_comp, comp_zero]

def ofSurjectionsIso : (ofSurjections R B X q hq).value R B ≅ X := by
  refine HomologicalComplex.Hom.isoOfComponents (quotientComponentIso R B X q hq) ?_
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  dsimp only [value]
  rw [CochainComplex.of_d]
  dsimp only [ofSurjections]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded
end

end ComplexFromSurjections

/-! ## CategoryCode（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryCode.lean） -/

/-!
概要：κ の ordinal 初期区間と固定基底の商 Hom を持つ dg 圏の小さい提示型。
方針：Hom の複体コード・実単位・実合成と三法則を保持し、主 dg 圏に評価する。
規約：任意の dg 圏構造を大きい宇宙のフィールドとして保存しない。
使われ方：16時間試作の、出発圏・seed・延長ラベルを保持する厳密関手的模型。
-/

@[expose] public section CategoryCode
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})

structure DGCategoryPresentationCode where
  ordinal : κ.ord.ToType
  hom : Set.Iio ordinal → Set.Iio ordinal → DGComplexPresentationCode R κ.ord.ToType
  unit : ∀ x, 𝟙_ (Complex R) ⟶ (hom x x).value R κ.ord.ToType
  comp : ∀ x y z, (hom x y).value R κ.ord.ToType ⊗ (hom y z).value R κ.ord.ToType ⟶
    (hom x z).value R κ.ord.ToType
  left : ∀ x y, (λ_ ((hom x y).value R κ.ord.ToType)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _
  right : ∀ x y, (ρ_ ((hom x y).value R κ.ord.ToType)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _
  assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
    _ ◁ comp x y z ≫ comp w x z

namespace DGCategoryPresentationCode

def Objects (c : DGCategoryPresentationCode R κ) : Type u := Set.Iio c.ordinal

instance enrichment (c : DGCategoryPresentationCode R κ) : DGCategory R (c.Objects R κ) :=
  ofHomObjects R _ (fun x y => (c.hom x y).value R κ.ord.ToType)
    c.unit c.comp c.left c.right c.assoc

lemma small : Small.{u} (DGCategoryPresentationCode R κ) := inferInstance

end DGCategoryPresentationCode
end SerrePositivity.DifferentialGraded
end

end CategoryCode

/-! ## CategoryData（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryData.lean） -/

/-!
概要：固定基底の Hom 提示を任意の小さい対象型上に配置した圏データを保持する。
方針：元の提示コードと同じ単位・合成・三法則を保持し、対象の再添字と分離する。
規約：任意の Hom 複体や dg 圏構造を大きい宇宙のフィールドへ保存しない。
使われ方：二項・可算個の出発提示を非連結和へまとめる前の中間データ。
-/

@[expose] public section CategoryData
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (B X : Type u)

structure DGCategoryPresentationData where
  hom : X → X → DGComplexPresentationCode R B
  unit : ∀ x, 𝟙_ (Complex R) ⟶ (hom x x).value R B
  comp : ∀ x y z, (hom x y).value R B ⊗ (hom y z).value R B ⟶ (hom x z).value R B
  left : ∀ x y, (λ_ ((hom x y).value R B)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _
  right : ∀ x y, (ρ_ ((hom x y).value R B)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _
  assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
    _ ◁ comp x y z ≫ comp w x z

namespace DGCategoryPresentationData

@[instance_reducible] def enrichment (c : DGCategoryPresentationData R B X) : DGCategory R X :=
  ofHomObjects R X (fun x y => (c.hom x y).value R B)
    c.unit c.comp c.left c.right c.assoc

lemma small : Small.{u} (DGCategoryPresentationData R B X) := inferInstance

end DGCategoryPresentationData

namespace DGCategoryPresentationCode
variable (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

def toData : DGCategoryPresentationData R κ.ord.ToType (c.Objects R κ) where
  hom := c.hom
  unit := c.unit
  comp := c.comp
  left := c.left
  right := c.right
  assoc := c.assoc

end DGCategoryPresentationCode
end SerrePositivity.DifferentialGraded
end

end CategoryData

/-! ## CategoryReindex（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryReindex.lean） -/

/-!
概要：任意の小さい対象型上の提示データを、κ の指定初期区間へ再添字する。
方針：対象の同値で Hom 提示・単位・合成・三法則をそのまま引き戻す。
規約：対象の同値を入力に保持し、評価の全 Hom 作用は恒等にする。
使われ方：非連結和にまとめた出発提示を元の小さいコード型へ戻す。
-/

@[expose] public section CategoryReindex
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)

namespace DGCategoryPresentationData

def reindex : DGCategoryPresentationCode R κ where
  ordinal := a
  hom x y := c.hom (e x) (e y)
  unit x := c.unit (e x)
  comp x y z := c.comp (e x) (e y) (e z)
  left x y := c.left (e x) (e y)
  right x y := c.right (e x) (e y)
  assoc w x y z := c.assoc (e w) (e x) (e y) (e z)

def reindexEvaluation :
    letI := c.enrichment R κ.ord.ToType X
    DGFunctor R ((reindex R κ X c a e).Objects R κ) X := by
  letI := c.enrichment R κ.ord.ToType X
  exact {
    obj := e
    map _ _ := 𝟙 _
    map_id _ := Category.comp_id _
    map_comp _ _ _ := by
      simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl }

lemma reindexEvaluation_obj_surjective :
    letI := c.enrichment R κ.ord.ToType X
    Function.Surjective (reindexEvaluation R κ X c a e).obj := e.surjective

lemma reindexEvaluation_homIso (x y : (reindex R κ X c a e).Objects R κ) :
    letI := c.enrichment R κ.ord.ToType X
    IsIso ((reindexEvaluation R κ X c a e).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategoryReindex

/-! ## CategoryReindexInverse（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryReindexInverse.lean） -/

/-!
概要：提示の対象再添字を逆向きの全 Hom dg 関手として実現する。
方針：同値の逆写像を対象作用に保ち、評価後の等式同型で全次数を共役する。
規約：既存の一般共役入口を再利用し、提示の Hom データを選び直さない。
使われ方：非連結和の各成分を ordinal コードへ戻した共通提示へ包含する。
-/

@[expose] public section CategoryReindexInverse
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)
namespace DGCategoryPresentationData

def reindexInverse :
    letI := c.enrichment R κ.ord.ToType X
    DGFunctor R X ((reindex R κ X c a e).Objects R κ) := by
  letI := c.enrichment R κ.ord.ToType X
  exact inducedDGFunctorClosedConjugate R (id : X → X) (e : Set.Iio a → X)
    (DGFunctor.id X) e.symm (fun x =>
      eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))

lemma reindexInverse_obj (x : X) :
    letI := c.enrichment R κ.ord.ToType X
    (reindexInverse R κ X c a e).obj x = e.symm x := rfl

/-- 逆再添字の後の実評価は、元の全閉射関手と自然同型になる。 -/
def reindexInverseEvaluationIso :
    letI := c.enrichment R κ.ord.ToType X
    (DGFunctor.id X).onClosed ≅
      ((reindexInverse R κ X c a e).comp (reindexEvaluation R κ X c a e)).onClosed := by
  letI := c.enrichment R κ.ord.ToType X
  exact inducedDGFunctorClosedConjugateIso R (id : X → X) (e : Set.Iio a → X)
    (DGFunctor.id X) e.symm (fun x =>
      eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategoryReindexInverse

/-! ## CategoryReindexIdentity（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryReindexIdentity.lean） -/

/-!
概要：逆再添字の後の評価を、全 Hom を含む元の恒等 dg 関手と同定する。
方針：保持した等式同型の共役と、その逆の等式移送を相殺する。
規約：閉零射上の自然同型だけに弱めず、dg 関手の等式を証明する。
使われ方：κ-small 共通提示の各成分から元の評価関手を回収する。
-/

@[expose] public section CategoryReindexIdentity
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory KST.SConstruction
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (X : Type u)
  (c : DGCategoryPresentationData R κ.ord.ToType X) (a : κ.ord.ToType) (e : Set.Iio a ≃ X)
namespace DGCategoryPresentationData

lemma reindexInverse_comp_evaluation :
    letI := c.enrichment R κ.ord.ToType X
    (reindexInverse R κ X c a e).comp (reindexEvaluation R κ X c a e) =
      DGFunctor.id X := by
  letI := c.enrichment R κ.ord.ToType X
  apply EnrichedFunctor.ext (Complex R) (fun x => e.apply_symm_apply x)
  intro x y
  rw [inducedDGHom_eqToHom R (id : X → X)
    (e.apply_symm_apply x) (e.apply_symm_apply y)]
  change ((𝟙 _ ≫ 𝟙 _) ≫ enrichedClosedIsoConjugation (Complex R)
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x).symm))
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply y).symm))) ≫
      𝟙 _ ≫ enrichedClosedIsoConjugation (Complex R)
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply x)))
        (eqToIso (congrArg (ForgetEnrichment.of (Complex R)) (e.apply_symm_apply y))) = 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rw [enrichedClosedIsoConjugation_trans]
  simp [enrichedClosedIsoConjugation]

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
end

end CategoryReindexIdentity

/-! ## CategoryFromHomSurjections（旧 SerrePositivity/DifferentialGraded/Presentation/CategoryFromHomSurjections.lean） -/

/-!
概要：固定自由加群で被覆された Hom 複体を持つ小対象族を、dg 圏の提示コードへ戻す。
方針：各次数の商の同型で Hom を符号化し、元の dg 単位・合成・三法則を移送する。
規約：Hom の生成元被覆を明示入力とし、係数閉包の小ささを仮定なく結論しない。
使われ方：c′ の共通源係数精密化を固定基底の提示模型へ符号化する。
-/

@[expose] public section CategoryFromHomSurjections
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (value : Set.Iio a → D)
  (q : ∀ x y : Set.Iio a, ∀ n : ℤ,
    (κ.ord.ToType →₀ R) →ₗ[R] (homObject R D (value x) (value y)).X n)
  (hq : ∀ x y n, Function.Surjective (q x y n))

abbrev dgCategoryHomSurjectionCode (x y : Set.Iio a) :
    DGComplexPresentationCode R κ.ord.ToType :=
  DGComplexPresentationCode.ofSurjections R κ.ord.ToType
    (homObject R D (value x) (value y)) (q x y) (hq x y)

def dgCategoryHomSurjectionIso (x y : Set.Iio a) :
    (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType ≅
      homObject R D (value x) (value y) :=
  DGComplexPresentationCode.ofSurjectionsIso R κ.ord.ToType
    (homObject R D (value x) (value y)) (q x y) (hq x y)

def dgCategoryPresentationOfHomSurjections : DGCategoryPresentationCode R κ where
  ordinal := a
  hom := dgCategoryHomSurjectionCode R D κ a value q hq
  unit x := eId (Complex R) (value x) ≫ (dgCategoryHomSurjectionIso R D κ a value q hq x x).inv
  comp x y z :=
    ((dgCategoryHomSurjectionIso R D κ a value q hq x y).hom ⊗ₘ
      (dgCategoryHomSurjectionIso R D κ a value q hq y z).hom) ≫
    eComp (Complex R) (value x) (value y) (value z) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).inv
  left := by
    letI := inducedDGCategory R value
    exact dgHomTransport_left R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)
  right := by
    letI := inducedDGCategory R value
    exact dgHomTransport_right R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)
  assoc := by
    letI := inducedDGCategory R value
    exact dgHomTransport_assoc R (Set.Iio a)
      (fun x y => (dgCategoryHomSurjectionCode R D κ a value q hq x y).value R κ.ord.ToType)
      (dgCategoryHomSurjectionIso R D κ a value q hq)

def dgCategoryPresentationOfHomSurjectionsEvaluation :
    DGFunctor R ((dgCategoryPresentationOfHomSurjections R D κ a value q hq).Objects R κ) D where
  obj := value
  map x y := (dgCategoryHomSurjectionIso R D κ a value q hq x y).hom
  map_id x := by
    change (eId (Complex R) (value x) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x x).inv) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x x).hom = _
    simp
  map_comp x y z := by
    change (((dgCategoryHomSurjectionIso R D κ a value q hq x y).hom ⊗ₘ
      (dgCategoryHomSurjectionIso R D κ a value q hq y z).hom) ≫
      eComp (Complex R) (value x) (value y) (value z) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).inv) ≫
      (dgCategoryHomSurjectionIso R D κ a value q hq x z).hom = _
    simp

lemma dgCategoryPresentationOfHomSurjectionsEvaluation_homIso
    (x y : (dgCategoryPresentationOfHomSurjections R D κ a value q hq).Objects R κ) :
    IsIso ((dgCategoryPresentationOfHomSurjectionsEvaluation R D κ a value q hq).map x y) := by
  change IsIso (dgCategoryHomSurjectionIso R D κ a value q hq x y).hom
  infer_instance

end SerrePositivity.DifferentialGraded
end

end CategoryFromHomSurjections

/-! ## ZeroComplexCode（旧 SerrePositivity/DifferentialGraded/Presentation/ZeroComplexCode.lean） -/

/-!
概要：固定基底の全関係による零複体の提示コードを構成する。
方針：各次数を自由加群の全部分加群で割り、微分を零にする。
規約：台の型を変更せず、既存の小さい提示型を使う。
使われ方：出発提示の非連結和で異なる成分間の Hom を零にする。
-/

@[expose] public section ZeroComplexCode
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (B : Type u)

namespace DGComplexPresentationCode

def zero : DGComplexPresentationCode R B where
  relations _ := ⊤
  differential _ := 0
  square _ := zero_comp

lemma zero_value_isZero : IsZero ((zero R B).value R B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext n x
  change (x : (B →₀ R) ⧸ (⊤ : Submodule R (B →₀ R))) = 0
  exact @Subsingleton.elim ((B →₀ R) ⧸ (⊤ : Submodule R (B →₀ R)))
    ((Submodule.Quotient.subsingleton_iff).2 rfl) x 0

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded
end

end ZeroComplexCode
