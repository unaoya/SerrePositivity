module

public import SerrePositivity.DifferentialGraded.Functor.Components
public import Mathlib.LinearAlgebra.Span.Defs
public import SerrePositivity.DifferentialGraded.Category.FaithfulHomConstruction
public import SerrePositivity.DifferentialGraded.Category.Induced
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
public import Mathlib.Data.W.Cardinal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.Ordinal
public import SerrePositivity.DifferentialGraded.Presentation.Category
public import SerrePositivity.DifferentialGraded.Functor.FullHomLift
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finset.Card

/-!
# Presentation.GeneratedHom.CoefficientClosure

## 概要
係数語の dg 閉包、基数評価と固定基底コードへの持ち上げをまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## GeneratedHomWords（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomWords.lean） -/

/-!
概要：指定斉次係数から微分・単位・合成で作る有限語とその実 Hom 評価を与える。
方針：線形結合前の語を対象・次数で添字付けし、評価と dg 関手像の可換性を帰納する。
規約：語の型は係数値を保存せず、指定生成子と対象ラベルだけに依存する。
使われ方：c′ の閉射係数を含む dg 係数閉包の自由生成元の準備。
-/

@[expose] public section GeneratedHomWords
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)

inductive DGGeneratedHomWord : J → J → ℤ → Type u
  | unit (x : J) : DGGeneratedHomWord x x 0
  | generator (i : I) : DGGeneratedHomWord (source i) (target i) (degree i)
  | derivative {x y : J} {n : ℤ} (a : DGGeneratedHomWord x y n) :
      DGGeneratedHomWord x y (n + 1)
  | composition {x y z : J} {p q : ℤ}
      (a : DGGeneratedHomWord x y p) (b : DGGeneratedHomWord y z q) :
      DGGeneratedHomWord x z (p + q)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))

namespace DGGeneratedHomWord

def evaluate {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    GradedHom R (value x) (value y) n :=
  match a with
  | .unit x => (unitElement R (value x)).val
  | .generator i => coefficient i
  | .derivative a => differential R (evaluate a)
  | .composition a b => forward R (evaluate a)
      (evaluate b) rfl

variable (E : Type w) [DGCategory R E] (F : DGFunctor R D E)

lemma evaluate_map {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    (F.map (value x) (value y)).f n (evaluate source target degree R D value coefficient a) =
      evaluate source target degree R E (F.obj ∘ value)
        (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) a := by
  induction a with
  | unit x => exact DGFunctor.map_unitElement R F (value x)
  | generator i => rfl
  | @derivative x y n a ih =>
    change (F.map (value x) (value y)).f (n + 1)
      (differential R (evaluate source target degree R D value coefficient a)) = _
    have h := congrArg (fun k => k (evaluate source target degree R D value coefficient a))
      ((F.map (value x) (value y)).comm n (n + 1))
    change differential R ((F.map (value x) (value y)).f n
        (evaluate source target degree R D value coefficient a)) =
      (F.map (value x) (value y)).f (n + 1)
        (differential R (evaluate source target degree R D value coefficient a)) at h
    rw [← h, ih]
    rfl
  | composition a b iha ihb =>
    change (F.map _ _).f _ (forward R _ _ rfl) = _
    rw [DGFunctor.map_forward, iha, ihb]
    rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomWords

/-! ## GeneratedHomSpan（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSpan.lean） -/

/-!
概要：指定係数の有限語の線形 span は、単位・微分・合成で閉じた斉次 Hom 族を与える。
方針：語の構成子と span の一変数・二変数帰納法を使い、dg 関手像も照合する。
規約：生成係数をラベルで保持し、任意の閉射がこの span に入るとは仮定なく主張しない。
使われ方：c′ の dg 係数閉包と固定基底 Hom 提示への再符号化。
-/

@[expose] public section GeneratedHomSpan
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))

namespace DGGeneratedHomWord

def linearSpan (x y : J) (n : ℤ) : Submodule R (GradedHom R (value x) (value y) n) :=
  Submodule.span R (Set.range (evaluate source target degree R D value coefficient
    (x := x) (y := y) (n := n)))

lemma evaluate_mem_span {x y : J} {n : ℤ}
    (a : DGGeneratedHomWord source target degree x y n) :
    evaluate source target degree R D value coefficient a ∈
      linearSpan source target degree R D value coefficient x y n :=
  Submodule.subset_span ⟨a, rfl⟩

lemma differential_mem_span {x y : J} {n : ℤ} {f : GradedHom R (value x) (value y) n}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    differential R f ∈ linearSpan source target degree R D value coefficient x y (n + 1) := by
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact evaluate_mem_span source target degree R D value coefficient (.derivative a)
  | zero => simpa only [differential, map_zero] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).zero_mem
  | add f g _ _ hf hg =>
    simpa only [differential, map_add] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).add_mem hf hg
  | smul a f _ hf =>
    simpa only [differential, map_smul] using
      (linearSpan source target degree R D value coefficient x y (n + 1)).smul_mem a hf

lemma forward_mem_span {x y z : J} {p q : ℤ}
    {f : GradedHom R (value x) (value y) p} {g : GradedHom R (value y) (value z) q}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y p)
    (hg : g ∈ linearSpan source target degree R D value coefficient y z q) :
    forward R f g rfl ∈ linearSpan source target degree R D value coefficient x z (p + q) := by
  let S := linearSpan source target degree R D value coefficient x z (p + q)
  refine Submodule.span_induction₂ (p := fun f g _ _ => forward R f g rfl ∈ S)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · intro f g hf hg
    obtain ⟨a, rfl⟩ := hf
    obtain ⟨b, rfl⟩ := hg
    exact evaluate_mem_span source target degree R D value coefficient (.composition a b)
  · intro g _
    simpa [forward] using S.zero_mem
  · intro f _
    simpa [forward] using S.zero_mem
  · intro f f' g _ _ _ hf hf'
    simpa [forward, TensorProduct.add_tmul, map_add] using S.add_mem hf hf'
  · intro f g g' _ _ _ hg hg'
    simpa [forward, TensorProduct.tmul_add, map_add] using S.add_mem hg hg'
  · intro a f g _ _ hf
    simpa [forward, TensorProduct.smul_tmul, map_smul] using S.smul_mem a hf
  · intro a f g _ _ hg
    simpa [forward, TensorProduct.tmul_smul, map_smul] using S.smul_mem a hg

variable (E : Type w) [DGCategory R E] (F : DGFunctor R D E)

lemma map_mem_span {x y : J} {n : ℤ} {f : GradedHom R (value x) (value y) n}
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    (F.map (value x) (value y)).f n f ∈
      linearSpan source target degree R E (F.obj ∘ value)
        (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) x y n := by
  let S := linearSpan source target degree R E (F.obj ∘ value)
    (fun i => (F.map (value (source i)) (value (target i))).f (degree i) (coefficient i)) x y n
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    rw [evaluate_map]
    exact evaluate_mem_span source target degree R E _ _ a
  | zero => simpa only [map_zero] using S.zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using S.add_mem hf hg
  | smul a f _ hf => simpa only [map_smul] using S.smul_mem a hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomSpan

/-! ## GeneratedHomComplex（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomComplex.lean） -/

/-!
概要：微分で閉じた係数 span を実 Hom 複体として構成し、元の Hom 複体へ単射で比較する。
方針：各次数の submodule に元の微分を制限し、同じ微分二乗零を反映する。
規約：係数 span の型と実埋め込みを保持する。
使われ方：c′ の小さい dg 係数閉包の Hom 複体と忠実な評価。
-/

@[expose] public section GeneratedHomComplex
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

abbrev component (x y : J) (n : ℤ) : ModuleCat R :=
  ModuleCat.of R (linearSpan source target degree R D value coefficient x y n)

def componentDifferential (x y : J) (n : ℤ) :
    component source target degree R D value coefficient x y n ⟶
      component source target degree R D value coefficient x y (n + 1) :=
  ModuleCat.ofHom
    { toFun f := ⟨differential R f.val,
        differential_mem_span source target degree R D value coefficient f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' a f := Subtype.ext (map_smul _ _ _) }

def homComplex (x y : J) : Complex R :=
  CochainComplex.of (component source target degree R D value coefficient x y)
    (componentDifferential source target degree R D value coefficient x y) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      change (homObject R D (value x) (value y)).d (n + 1) (n + 1 + 1)
        ((homObject R D (value x) (value y)).d n (n + 1) f.val) = 0
      exact congrArg (fun k => k f.val)
        ((homObject R D (value x) (value y)).d_comp_d n (n + 1) (n + 1 + 1)))

def inclusion (x y : J) :
    homComplex source target degree R D value coefficient x y ⟶ homObject R D (value x) (value y) where
  f n := ModuleCat.ofHom (linearSpan source target degree R D value coefficient x y n).subtype
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    dsimp only [homComplex]
    rw [CochainComplex.of_d]
    rfl

instance inclusion_mono (x y : J) :
    Mono (inclusion source target degree R D value coefficient x y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomComplex

/-! ## GeneratedHomUnit（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomUnit.lean） -/

/-!
概要：係数 span の実 Hom 複体の単位を、元の閉単位元から構成する。
方針：単位語が span に入ることと微分零から単位複体の射を作り、実埋め込みで照合する。
規約：元の dg 単位の値を保持する。
使われ方：c′ の実 dg 係数閉包の単位鎖写像。
-/

@[expose] public section GeneratedHomUnit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

def homUnitCycle (x : J) : zeroCycles (homComplex source target degree R D value coefficient x x) :=
  ⟨⟨(unitElement R (value x)).val,
    evaluate_mem_span source target degree R D value coefficient (.unit x)⟩, by
      change (homComplex source target degree R D value coefficient x x).d 0 1 _ = 0
      apply Subtype.ext
      change differential R (unitElement R (value x)).val = 0
      exact (unitElement R (value x)).property⟩

def homUnit (x : J) : 𝟙_ (Complex R) ⟶ homComplex source target degree R D value coefficient x x :=
  unitFromCycle _ (homUnitCycle source target degree R D value coefficient x)

lemma homUnit_inclusion (x : J) :
    homUnit source target degree R D value coefficient x ≫
      inclusion source target degree R D value coefficient x x = eId (Complex R) (value x) := by
  apply (unitCycleEquiv _).injective
  change cycleFromUnit _ (_ ≫ _) = unitElement R (value x)
  apply Subtype.ext
  rw [cycleFromUnit_postcomp]
  rw [homUnit, cycleFromUnit_unitFromCycle]
  rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomUnit

/-! ## GeneratedHomComposition（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomComposition.lean） -/

/-!
概要：係数 span の Hom 複体に元の斉次合成を制限する。
方針：二変数の線形性と微分の Leibniz 式を反映し、非有界 tensor の普遍性で束ねる。
規約：合成の向きと符号は元の豊穣順を保持する。
使われ方：c′ の実 dg 係数閉包の合成鎖写像。
-/

@[expose] public section GeneratedHomComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

def forwardComponent (x y z : J) (p q n : ℤ) (hn : p + q = n) :
    component source target degree R D value coefficient x y p ⊗
      component source target degree R D value coefficient y z q ⟶
        component source target degree R D value coefficient x z n :=
  ModuleCat.ofHom (TensorProduct.lift
    { toFun f :=
        { toFun g := ⟨forward R f.val g.val hn, by
            subst n
            exact forward_mem_span source target degree R D value coefficient f.property g.property⟩
          map_add' g g' := by
            apply Subtype.ext
            simp [forward, TensorProduct.tmul_add]
          map_smul' a g := by
            apply Subtype.ext
            simp [forward, TensorProduct.tmul_smul] }
      map_add' f f' := by
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        simp [forward, TensorProduct.add_tmul]
      map_smul' a f := by
        apply LinearMap.ext
        intro g
        apply Subtype.ext
        simp [forward, TensorProduct.smul_tmul] })

lemma forwardComponent_differential (x y z : J) (p q : ℤ) :
    forwardComponent source target degree R D value coefficient x y z p q (p + q) rfl ≫
      componentDifferential source target degree R D value coefficient x z (p + q) =
    (componentDifferential source target degree R D value coefficient x y p ▷
      component source target degree R D value coefficient y z q) ≫
      forwardComponent source target degree R D value coefficient x y z
        (p + 1) q (p + q + 1) (by omega) +
    p.negOnePow • (component source target degree R D value coefficient x y p ◁
      componentDifferential source target degree R D value coefficient y z q) ≫
      forwardComponent source target degree R D value coefficient x y z
        p (q + 1) (p + q + 1) (by omega) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  change differential R (forward R f.val g.val rfl) =
    forward R (differential R f.val) g.val (by omega) +
      p.negOnePow • forward R f.val (differential R g.val) (by omega)
  exact differential_forward R f.val g.val rfl

def homComposition (x y z : J) :
    homComplex source target degree R D value coefficient x y ⊗
      homComplex source target degree R D value coefficient y z ⟶
        homComplex source target degree R D value coefficient x z :=
  tensorLift (forwardComponent source target degree R D value coefficient x y z)
    (by
      intro p q
      simpa only [homComplex, CochainComplex.of_d] using
        forwardComponent_differential source target degree R D value coefficient x y z p q)

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomComposition

/-! ## GeneratedHomCategory（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomCategory.lean） -/

/-!
概要：指定斉次係数の単位・微分・合成閉包を実 dg 圏として構成する。
方針：係数 span の Hom 複体と制限合成から、単射比較で三法則を反映する。
規約：対象ラベルと元の実 Hom への忠実な評価を保持する。
使われ方：c′ の共通出発圏の係数精密化と固定基底コードへの輸送。
-/

@[expose] public section GeneratedHomCategory
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

lemma homComposition_inclusion (x y z : J) :
    homComposition source target degree R D value coefficient x y z ≫
      inclusion source target degree R D value coefficient x z =
    (inclusion source target degree R D value coefficient x y ⊗ₘ
      inclusion source target degree R D value coefficient y z) ≫
      eComp (Complex R) (value x) (value y) (value z) := by
  apply tensorHom_ext
  intro p q n hn
  simp only [homComposition, HomologicalComplex.comp_f, ι_tensorLift_assoc,
    ι_tensorHom_assoc, Category.assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  rfl

@[instance_reducible] def category : DGCategory R J := by
  letI := inducedDGCategory R value
  exact dgCategoryOfFaithfulHomMaps R J
    (homComplex source target degree R D value coefficient)
    (inclusion source target degree R D value coefficient)
    (homUnit source target degree R D value coefficient)
    (homComposition source target degree R D value coefficient)
    (homUnit_inclusion source target degree R D value coefficient)
    (homComposition_inclusion source target degree R D value coefficient)

def evaluation :
    letI := category source target degree R D value coefficient
    DGFunctor R J D := by
  letI := category source target degree R D value coefficient
  exact
    { obj := value
      map := inclusion source target degree R D value coefficient
      map_id := homUnit_inclusion source target degree R D value coefficient
      map_comp := homComposition_inclusion source target degree R D value coefficient }

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomCategory

/-! ## GeneratedHomFunctorLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomFunctorLift.lean） -/

/-!
概要：全 Hom 像が指定係数 span に入る dg 関手を、同じ実 dg 係数閉包へ持ち上げる。
方針：Hom 鎖写像を span へ制限し、忠実な評価で単位・合成を反映する。
規約：元の対象写像と全 Hom 作用を厳密に保持する。
使われ方：c′ の共通係数閉包に元の出発 dg 関手を収容する。
-/

@[expose] public section GeneratedHomFunctorLift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord
variable (C : Type w) [DGCategory R C]
  (F : DGFunctor R C (DGObjectImage value))
  (hF : ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
    linearSpan source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) n)

def liftHom (x y : C) : homObject R C x y ⟶
    homComplex source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) where
  f n := ModuleCat.ofHom (((F.map x y).f n).hom.codRestrict
    (linearSpan source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) n) (hF x y n))
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    dsimp only [homComplex]
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun k => k f) ((F.map x y).comm n (n + 1))

lemma liftHom_inclusion (x y : C) :
    liftHom source target degree R D value coefficient C F hF x y ≫
      inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) = F.map x y := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

def liftFunctor :
    letI := category source target degree R D value coefficient
    DGFunctor R C J := by
  letI := category source target degree R D value coefficient
  exact
    { obj := fun x => (F.obj x).label
      map := liftHom source target degree R D value coefficient C F hF
      map_id x := by
        apply (cancel_mono (inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label))).1
        change (eId (Complex R) x ≫ liftHom source target degree R D value coefficient C F hF x x) ≫
          inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label) =
          homUnit source target degree R D value coefficient ((F.obj x).label) ≫
            inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label)
        rw [Category.assoc, liftHom_inclusion, homUnit_inclusion]
        exact F.map_id x
      map_comp x y z := by
        apply (cancel_mono (inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label))).1
        change (eComp (Complex R) x y z ≫
          liftHom source target degree R D value coefficient C F hF x z) ≫
          inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label) =
          (liftHom source target degree R D value coefficient C F hF x y ⊗ₘ
            liftHom source target degree R D value coefficient C F hF y z) ≫
            homComposition source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) ((F.obj z).label) ≫
              inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label)
        simp only [Category.assoc, liftHom_inclusion, homComposition_inclusion]
        rw [tensorHom_comp_tensorHom_assoc, liftHom_inclusion, liftHom_inclusion]
        exact F.map_comp x y z }

lemma liftFunctor_comp_evaluation :
    letI := category source target degree R D value coefficient
    (liftFunctor source target degree R D value coefficient C F hF).comp
      (evaluation source target degree R D value coefficient) = F.comp (dgObjectImageEvaluation R value) := by
  letI := category source target degree R D value coefficient
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomFunctorLift

/-! ## GeneratedHomWordCardinality（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomWordCardinality.lean） -/

/-!
概要：係数の有限語の個数は、指定生成子・対象ラベルと可算集合の最大で抑えられる。
方針：単位・生成子・微分・合成の有限分岐 W 型へ忠実に符号化する。
規約：環の元の個数を上界に含めず、線形 span の生成元数を評価する。
使われ方：c′ の係数閉包を κ 個の固定基底で被覆するための語の小ささ。
-/

@[expose] public section GeneratedHomWordCardinality
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)

inductive DGGeneratedHomSymbol (I J : Type u)
  | unit (x : J)
  | generator (i : I)
  | derivative
  | composition

namespace DGGeneratedHomSymbol

def arity : DGGeneratedHomSymbol I J → Type u
  | .unit _ => ULift (Fin 0)
  | .generator _ => ULift (Fin 0)
  | .derivative => ULift (Fin 1)
  | .composition => ULift (Fin 2)

instance finite_arity (s : DGGeneratedHomSymbol I J) : Finite s.arity := by
  cases s <;> dsimp [arity] <;> infer_instance

def toSum : DGGeneratedHomSymbol I J → J ⊕ I ⊕ ULift.{u} Bool
  | .unit x => .inl x
  | .generator i => .inr (.inl i)
  | .derivative => .inr (.inr (ULift.up false))
  | .composition => .inr (.inr (ULift.up true))

lemma toSum_injective : Function.Injective (toSum (I := I) (J := J)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [toSum]

end DGGeneratedHomSymbol
namespace DGGeneratedHomWord

def encode {x y : J} {n : ℤ} (a : DGGeneratedHomWord source target degree x y n) :
    WType (DGGeneratedHomSymbol.arity (I := I) (J := J)) :=
  match a with
  | .unit x => .mk (.unit x) (fun i => Fin.elim0 i.down)
  | .generator i => .mk (.generator i) (fun j => Fin.elim0 j.down)
  | .derivative a => .mk .derivative (fun _ => encode a)
  | .composition a b => .mk .composition (fun i => if i.down = 0 then encode a else encode b)

lemma encode_heq {x y x' y' : J} {n n' : ℤ}
    (a : DGGeneratedHomWord source target degree x y n)
    (other : DGGeneratedHomWord source target degree x' y' n')
    (h : encode source target degree a = encode source target degree other) : x = x' ∧ y = y' ∧ n = n' ∧ HEq a other := by
  induction a generalizing x' y' n' with
  | unit x =>
    cases other <;> simp_all [encode, WType.mk.injEq]
    obtain ⟨rfl, _⟩ := h
    exact HEq.rfl
  | generator i =>
    cases other <;> simp_all [encode, WType.mk.injEq]
    obtain ⟨rfl, _⟩ := h
    exact HEq.rfl
  | derivative a ih =>
    cases other <;> simp only [encode, WType.mk.injEq, reduceCtorEq,
      false_and, and_false, true_and] at h
    have hf := h
    have he := congrFun (eq_of_heq hf) (ULift.up (0 : Fin 1))
    obtain ⟨rfl, rfl, rfl, hh⟩ := ih _ he
    cases eq_of_heq hh
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  | composition a b iha ihb =>
    cases other <;> simp only [encode, WType.mk.injEq, reduceCtorEq,
      false_and, and_false, true_and] at h
    have hf := h
    have h₀ := congrFun (eq_of_heq hf) (ULift.up (0 : Fin 2))
    have h₁ := congrFun (eq_of_heq hf) (ULift.up (1 : Fin 2))
    simp at h₀ h₁
    obtain ⟨rfl, rfl, rfl, ha⟩ := iha _ h₀
    obtain ⟨_, rfl, rfl, hb⟩ := ihb _ h₁
    cases eq_of_heq ha
    cases eq_of_heq hb
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩

lemma encode_injective (x y : J) (n : ℤ) :
    Function.Injective (encode source target degree (x := x) (y := y) (n := n)) :=
  fun a b h => eq_of_heq (encode_heq source target degree a b h).2.2.2

lemma cardinalMk_le (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hI : Cardinal.mk I ≤ κ) (hJ : Cardinal.mk J ≤ κ) (x y : J) (n : ℤ) :
    Cardinal.mk (DGGeneratedHomWord source target degree x y n) ≤ κ := by
  apply (Cardinal.mk_le_of_injective (encode_injective source target degree x y n)).trans
  apply WType.cardinalMk_le_max_aleph0_of_finite.trans
  apply max_le _ hκ
  apply (Cardinal.mk_le_of_injective (DGGeneratedHomSymbol.toSum_injective
    (I := I) (J := J))).trans
  simp only [Cardinal.mk_sum, Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ hJ (Cardinal.add_le_of_le hκ hI
    (Cardinal.mk_le_aleph0.trans hκ))

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomWordCardinality

/-! ## GeneratedHomFreeCover（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomFreeCover.lean） -/

/-!
概要：係数語の線形 span を固定した κ 個の自由基底で全射に被覆する。
方針：語の埋め込みを零で延長し、有限線形結合と span 帰納で全射性を示す。
規約：環の元の個数の上界は不要。語の生成子数と対象数だけを入力に保持する。
使われ方：c′ の実係数閉包を既存の固定基底 Hom 提示へ符号化する。
-/

@[expose] public section GeneratedHomFreeCover
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord
variable {x y : J} {n : ℤ} {B : Type u}
  (e : DGGeneratedHomWord source target degree x y n ↪ B)

def freeCoverValues : B → linearSpan source target degree R D value coefficient x y n :=
  Function.extend e
    (fun a => ⟨evaluate source target degree R D value coefficient a,
      evaluate_mem_span source target degree R D value coefficient a⟩) (fun _ => 0)

def freeCover : (B →₀ R) →ₗ[R] linearSpan source target degree R D value coefficient x y n :=
  Finsupp.linearCombination R (freeCoverValues source target degree R D value coefficient e)

lemma freeCover_surjective :
    Function.Surjective (freeCover source target degree R D value coefficient e) := by
  intro a
  let L := freeCover source target degree R D value coefficient e
  have h : ∀ z (hz : z ∈ linearSpan source target degree R D value coefficient x y n),
      (⟨z, hz⟩ : linearSpan source target degree R D value coefficient x y n) ∈
        LinearMap.range L := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      refine ⟨Finsupp.single (e w) 1, ?_⟩
      change Finsupp.linearCombination R _ (Finsupp.single (e w) 1) = _
      rw [Finsupp.linearCombination_single]
      simp only [freeCoverValues, Function.Injective.extend_apply e.injective, one_smul]
    | zero => exact (LinearMap.range L).zero_mem
    | add f g _ _ hf hg => exact (LinearMap.range L).add_mem hf hg
    | smul a f _ hf => exact (LinearMap.range L).smul_mem a hf
  exact h a.val a.property

lemma fixedFreeCover_exists (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hI : Cardinal.mk I ≤ κ) (hJ : Cardinal.mk J ≤ κ) (x y : J) (n : ℤ) :
    ∃ q : (κ.ord.ToType →₀ R) →ₗ[R]
        linearSpan source target degree R D value coefficient x y n, Function.Surjective q := by
  have hcard : Cardinal.mk (DGGeneratedHomWord source target degree x y n) ≤
      Cardinal.mk κ.ord.ToType := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact cardinalMk_le source target degree κ hκ hI hJ x y n
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hcard
  exact ⟨freeCover source target degree R D value coefficient e,
    freeCover_surjective source target degree R D value coefficient e⟩

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomFreeCover

/-! ## GeneratedHomCode（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomCode.lean） -/

/-!
概要：κ 個以下の指定係数の dg 閉包を既存の小出発提示コードへ符号化する。
方針：閉包の各 Hom に固定自由被覆を選び、全 Hom 同型を保つ提示と実評価を合成する。
規約：出発対象の ordinal ラベルと元の実 Hom への単射性を保持する。
使われ方：c′ の任意閉射を含む係数精密化で使う共通出発コードの構成。
-/

@[expose] public section GeneratedHomCode
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord

include hκ hI in
lemma fixedFreeCover_ordinal (x y : Set.Iio a) (n : ℤ) :
    ∃ q : (κ.ord.ToType →₀ R) →ₗ[R]
      linearSpan source target degree R D value coefficient x y n, Function.Surjective q :=
  fixedFreeCover_exists source target degree R D value coefficient κ hκ hI
    (le_of_lt (by simpa using Cardinal.mk_Iio_lt a (by simp))) x y n

def ordinalCover (x y : Set.Iio a) (n : ℤ) :
    (κ.ord.ToType →₀ R) →ₗ[R] linearSpan source target degree R D value coefficient x y n :=
  (fixedFreeCover_ordinal R D κ a source target degree value coefficient hκ hI x y n).choose

lemma ordinalCover_surjective (x y : Set.Iio a) (n : ℤ) :
    Function.Surjective (ordinalCover R D κ a source target degree value coefficient hκ hI x y n) :=
  (fixedFreeCover_ordinal R D κ a source target degree value coefficient hκ hI x y n).choose_spec

def code : DGCategoryPresentationCode R κ := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjections R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)

def codeEvaluation : DGFunctor R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) D := by
  letI := category source target degree R D value coefficient
  exact (dgCategoryPresentationOfHomSurjectionsEvaluation R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)).comp
      (evaluation source target degree R D value coefficient)

lemma codeEvaluation_obj
    (x : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).obj x = value x := rfl

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomCode

/-! ## GeneratedHomCodeFaithful（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomCodeFaithful.lean） -/

/-!
概要：係数閉包の固定基底コードの評価は、全 Hom 複体で単射である。
方針：商による提示と係数 span の同型の後に、元の Hom への単射を合成する。
規約：対象ラベルの重複を許し、充満性を仮定しない。
使われ方：c′ の出発関手と閉射の係数精密化の等式を実 dg 圏で反映する。
-/

@[expose] public section GeneratedHomCodeFaithful
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord

lemma codeEvaluation_homMono
    (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    Mono ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y) := by
  let e : homObject R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y ≅
      homComplex source target degree R D value coefficient x y := by
    letI := category source target degree R D value coefficient
    exact dgCategoryHomSurjectionIso R (Set.Iio a) κ a id
      (ordinalCover R D κ a source target degree value coefficient hκ hI)
      (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI) x y
  change Mono (e.hom ≫ inclusion source target degree R D value coefficient x y)
  infer_instance

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomCodeFaithful

/-! ## GeneratedHomCodeFunctorLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomCodeFunctorLift.lean） -/

/-!
概要：指定係数閉包に入る元の出発 dg 関手を固定基底の共通コードへ持ち上げる。
方針：実係数閉包への持ち上げを、コードの全 Hom 同型の逆で輸送する。
規約：元の対象ラベルと全 Hom 上の実評価の厳密な因子化を保持する。
使われ方：c′ の元の出発提示と任意閉射を同時に含む精密化の出発関手。
-/

@[expose] public section GeneratedHomCodeFunctorLift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord

def codeToClosure :
    letI := category source target degree R D value coefficient
    DGFunctor R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ)
      (Set.Iio a) := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjectionsEvaluation R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)

lemma codeToClosure_homIso
    (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    letI := category source target degree R D value coefficient
    IsIso ((codeToClosure R D κ a source target degree value coefficient hκ hI).map x y) := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjectionsEvaluation_homIso R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI) x y

variable (C : Type w) [DGCategory R C] (F : DGFunctor R C (DGObjectImage value))
  (hF : ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
    linearSpan source target degree R D value coefficient (F.obj x).label (F.obj y).label n)

def codeFunctorLift : DGFunctor R C
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) := by
  letI := category source target degree R D value coefficient
  let G := liftFunctor source target degree R D value coefficient C F hF
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  exact dgFunctorFullHomLift R _ _ L
    (codeToClosure_homIso R D κ a source target degree value coefficient hκ hI) C
    (fun x => (F.obj x).label) G.map G.map_id G.map_comp

lemma codeFunctorLift_map (x y : C) :
    letI := category source target degree R D value coefficient
    (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).map x y ≫
      (codeToClosure R D κ a source target degree value coefficient hκ hI).map
        (F.obj x).label (F.obj y).label =
      liftHom source target degree R D value coefficient C F hF x y := by
  letI := category source target degree R D value coefficient
  exact dgFunctorFullHomLift_map R _ _
    (codeToClosure R D κ a source target degree value coefficient hκ hI)
    (codeToClosure_homIso R D κ a source target degree value coefficient hκ hI) C
    (fun x => (F.obj x).label)
    (liftFunctor source target degree R D value coefficient C F hF).map
    (liftFunctor source target degree R D value coefficient C F hF).map_id
    (liftFunctor source target degree R D value coefficient C F hF).map_comp x y

lemma codeFunctorLift_comp_evaluation :
    (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).comp
      (codeEvaluation R D κ a source target degree value coefficient hκ hI) =
      F.comp (dgObjectImageEvaluation R value) := by
  letI := category source target degree R D value coefficient
  apply EnrichedFunctor.ext (Complex R)
    (F := (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).comp
      (codeEvaluation R D κ a source target degree value coefficient hκ hI))
    (G := F.comp (dgObjectImageEvaluation R value)) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]
  change (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).map x y ≫
    ((codeToClosure R D κ a source target degree value coefficient hκ hI).map
      (F.obj x).label (F.obj y).label ≫
      inclusion source target degree R D value coefficient (F.obj x).label (F.obj y).label) = F.map x y
  rw [← Category.assoc, codeFunctorLift_map, liftHom_inclusion]

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomCodeFunctorLift

/-! ## GeneratedHomCochainLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomCochainLift.lean） -/

/-!
概要：係数 span に入る斉次射を固定基底コードへ持ち上げ、実評価と閉性を厳密に保持する。
方針：コードから係数閉包への Hom 同型の逆で持ち上げ、単射な実評価で微分零を反映する。
規約：全次数と元の端点ラベルを保持する。
使われ方：c′ の追加係数から実閉射・cone の精密化を回収する。
-/

@[expose] public section GeneratedHomCochainLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)

def codeCochainLift (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) : GradedHom R x y n := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  exact (inv (L.map x y)).f n ⟨f, hf⟩

lemma codeCochainLift_map (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n
      (codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf) = f := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  change (inclusion source target degree R D value coefficient x y).f n
    ((L.map x y).f n ((inv (L.map x y)).f n ⟨f, hf⟩)) = f
  have h := congrArg (fun k => k.f n ⟨f, hf⟩) (IsIso.inv_hom_id (L.map x y))
  change (L.map x y).f n ((inv (L.map x y)).f n ⟨f, hf⟩) = ⟨f, hf⟩ at h
  rw [h]
  rfl

lemma codeEvaluation_degree_injective (n : ℤ) :
    Function.Injective (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n) := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  haveI : IsIso ((L.map x y).f n) := by
    change IsIso ((HomologicalComplex.eval (ModuleCat R) (.up ℤ) n).map (L.map x y))
    infer_instance
  intro f g h
  apply (ModuleCat.mono_iff_injective ((L.map x y).f n)).1 inferInstance
  apply Subtype.ext
  exact h

lemma codeCochainLift_differential (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n)
    (hz : differential R f = 0) :
    differential R (codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf) = 0 := by
  apply codeEvaluation_degree_injective R D κ a source target degree value coefficient hκ hI x y (n + 1)
  rw [map_zero]
  let g := codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf
  have h := congrArg (fun k => k g)
    (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).comm n (n + 1))
  change differential R (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n g) =
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f (n + 1) (differential R g) at h
  rw [← h, codeCochainLift_map]
  exact hz

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomCochainLift

/-! ## GeneratedHomClosedLift（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomClosedLift.lean） -/

/-!
概要：係数 span に入る元の閉次数零射をコードの実閉射へ持ち上げる。
方針：閉射の零 cycle を同じ次数で持ち上げ、単位複体からの射へ戻す。
規約：実評価後に元の同じ閉射へ厳密に一致させる。
使われ方：c′ の追加係数から実関手と閉射を同時に回収する。
-/

@[expose] public section GeneratedHomClosedLift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)
  (f : ForgetEnrichment.of (Complex R) (value x) ⟶ ForgetEnrichment.of (Complex R) (value y))
  (hf : (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val ∈
    linearSpan source target degree R D value coefficient x y 0)

def codeClosedLiftCycle : zeroCycles (homObject R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y) :=
  ⟨codeCochainLift R D κ a source target degree value coefficient hκ hI x y 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val hf,
    codeCochainLift_differential R D κ a source target degree value coefficient hκ hI x y 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val hf
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).property⟩

def codeClosedLift : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
  ForgetEnrichment.homOf (Complex R)
    (unitFromCycle _ (codeClosedLiftCycle R D κ a source target degree value coefficient hκ hI x y f hf))

lemma codeClosedLift_map :
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).onClosed.map
      (codeClosedLift R D κ a source target degree value coefficient hκ hI x y f hf) = f := by
  change unitFromCycle _ (codeClosedLiftCycle R D κ a source target degree value coefficient hκ hI x y f hf) ≫
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y =
      ForgetEnrichment.homTo (Complex R) f
  apply (unitCycleEquiv _).injective
  change cycleFromUnit _ (_ ≫ _) = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)
  apply Subtype.ext
  rw [cycleFromUnit_postcomp, cycleFromUnit_unitFromCycle]
  exact codeCochainLift_map R D κ a source target degree value coefficient hκ hI x y 0 _ hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
end

end GeneratedHomClosedLift

/-! ## QuotientGeneratorImage（旧 SerrePositivity/DifferentialGraded/Presentation/QuotientGeneratorImage.lean） -/

/-!
概要：固定自由加群の商からの線形写像の像が指定 submodule に入ることを基底で判定する。
方針：商への全射で元を持ち上げ、有限支持線形結合の帰納を使う。
規約：関係部分加群の生成元数を制限しない。
使われ方：c′ の元の出発 Hom 提示の全像を κ 個の係数で係数閉包に含める。
-/

@[expose] public section QuotientGeneratorImage
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
variable {R B : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

lemma quotientGeneratorImage_mem (P : Submodule R (B →₀ R))
    (L : ((B →₀ R) ⧸ P) →ₗ[R] M) (S : Submodule R M)
    (h : ∀ b, L (P.mkQ (Finsupp.single b 1)) ∈ S) (x : (B →₀ R) ⧸ P) : L x ∈ S := by
  obtain ⟨v, rfl⟩ := P.mkQ_surjective x
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using S.zero_mem
  | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
  | single b r =>
    have hs : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    rw [hs, map_smul, map_smul]
    exact S.smul_mem r (h b)

end SerrePositivity.DifferentialGraded
end

end QuotientGeneratorImage

/-! ## FiniteRowCoefficientBound（旧 SerrePositivity/DifferentialGraded/Presentation/FiniteRowCoefficientBound.lean） -/

/-!
概要：κ個以下の行に有限個ずつ現れる係数の総数をκで抑える。
方針：有限 support の直和の基数を、行数とκの積で評価する。
規約：列全体の基数と係数環の基数は仮定しない。
使われ方：c′ の自由直和間閉射の係数をκ提示へ取り込む。
-/

@[expose] public section FiniteRowCoefficientBound
universe u

namespace SerrePositivity.DifferentialGraded

lemma finiteRowCoefficientIndex_cardinal_le {I J : Type u} (support : I → Finset J)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => Cardinal.mk (support i : Set J)) ≤
        Cardinal.sum (fun _ : I => κ) :=
      Cardinal.sum_le_sum _ _ (fun i => (Cardinal.lt_aleph0_of_finite (support i : Set J)).le.trans hκ)
    _ = Cardinal.mk I * κ := Cardinal.sum_const' I κ
    _ ≤ κ := Cardinal.mul_le_of_le hκ hI le_rfl

end SerrePositivity.DifferentialGraded

end FiniteRowCoefficientBound

/-! ## GeneratedHomSourceContainment（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSourceContainment.lean） -/

/-!
概要：元の出発提示の各 Hom の全像は、固定基底の像を含めるだけで係数閉包に入る。
方針：提示の商による Hom をその固定自由基底へ戻し、線形像の span 帰納を使う。
規約：元の dg 関手と関係部分加群を保持し、関係の個数を制限しない。
使われ方：c′ の元の二つの出発圏を共通係数閉包へ含めるための全 Hom 判定。
-/

@[expose] public section GeneratedHomSourceContainment
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

def dgCodeHomGenerator (x y : c.Objects R κ) (n : ℤ) (b : κ.ord.ToType) : GradedHom R x y n :=
  ((c.hom x y).relations n).mkQ (Finsupp.single b 1)

variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))

lemma generatedHomImage_of_codeGenerators
    (hgen : ∀ x y n b, (F.map x y).f n (dgCodeHomGenerator R κ c x y n b) ∈
      DGGeneratedHomWord.linearSpan source target degree R D value coefficient
        (F.obj x).label (F.obj y).label n) :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan source target degree R D value coefficient
        (F.obj x).label (F.obj y).label n := by
  intro x y n f
  exact quotientGeneratorImage_mem ((c.hom x y).relations n) ((F.map x y).f n).hom
    (DGGeneratedHomWord.linearSpan source target degree R D value coefficient
      (F.obj x).label (F.obj y).label n) (hgen x y n) f

end SerrePositivity.DifferentialGraded
end

end GeneratedHomSourceContainment

/-! ## GeneratedHomSourceGenerators（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomSourceGenerators.lean） -/

/-!
概要：元の小出発提示の全 Hom 像を含む κ 個以下の指定係数族を構成する。
方針：対象対・整数次数・固定自由基底で係数を添字付けし、基底像から全像を回収する。
規約：元の関係部分加群と実 dg 関手を保持する。
使われ方：c′ の共通係数閉包へ元の出発提示を収容する基底族。
-/

@[expose] public section GeneratedHomSourceGenerators
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

abbrev DGCodeHomGeneratorIndex : Type u :=
  c.Objects R κ × c.Objects R κ × ULift.{u} ℤ × κ.ord.ToType

lemma dgCodeHomGeneratorIndex_cardinal_le (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (DGCodeHomGeneratorIndex R κ c) ≤ κ := by
  have hO : Cardinal.mk (c.Objects R κ) ≤ κ := le_of_lt
    (by simpa only [DGCategoryPresentationCode.Objects, Cardinal.mk_toType, Cardinal.card_ord] using Cardinal.mk_Iio_lt c.ordinal (by simp))
  have hZ : Cardinal.mk (ULift.{u} ℤ) ≤ κ := Cardinal.mk_le_aleph0.trans hκ
  simp only [DGCodeHomGeneratorIndex, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_toType, Cardinal.card_ord]
  exact Cardinal.mul_le_of_le hκ hO
    (Cardinal.mul_le_of_le hκ hO (Cardinal.mul_le_of_le hκ hZ le_rfl))

variable {J : Type u} (D : Type v) [DGCategory R D] (value : J → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))

def dgCodeGeneratorSource (i : DGCodeHomGeneratorIndex R κ c) : J := (F.obj i.1).label

def dgCodeGeneratorTarget (i : DGCodeHomGeneratorIndex R κ c) : J := (F.obj i.2.1).label

def dgCodeGeneratorDegree (i : DGCodeHomGeneratorIndex R κ c) : ℤ := i.2.2.1.down

def dgCodeGeneratorCoefficient (i : DGCodeHomGeneratorIndex R κ c) :
    GradedHom R (value (dgCodeGeneratorSource R κ c D value F i))
      (value (dgCodeGeneratorTarget R κ c D value F i)) (dgCodeGeneratorDegree R κ c i) :=
  (F.map i.1 i.2.1).f i.2.2.1.down (dgCodeHomGenerator R κ c i.1 i.2.1 i.2.2.1.down i.2.2.2)

lemma dgCodeGeneratorImage_contains :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan (dgCodeGeneratorSource R κ c D value F)
        (dgCodeGeneratorTarget R κ c D value F) (dgCodeGeneratorDegree R κ c) R D value
        (dgCodeGeneratorCoefficient R κ c D value F) (F.obj x).label (F.obj y).label n := by
  apply generatedHomImage_of_codeGenerators R κ c _ _ _ D value _ F
  intro x y n b
  exact DGGeneratedHomWord.evaluate_mem_span _ _ _ R D value
    (dgCodeGeneratorCoefficient R κ c D value F) (.generator ⟨x, y, ULift.up n, b⟩)

end SerrePositivity.DifferentialGraded
end

end GeneratedHomSourceGenerators

/-! ## GeneratedHomAugmentedCoefficients（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomAugmentedCoefficients.lean） -/

/-!
概要：元の出発提示の全基底像に追加係数を併合し、同じ κ 上界と全 Hom 包含を保つ。
方針：係数族の直和で基底像と追加係数を保持し、各生成子語を span へ送る。
規約：元の dg 関手の全 Hom を省略せず、追加係数の個数だけを仮定する。
使われ方：c′ の任意閉射に必要な係数を共通の出発提示へ取り込む。
-/

@[expose] public section GeneratedHomAugmentedCoefficients
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  {J K : Type u} (D : Type v) [DGCategory R D] (value : J → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (extraSource extraTarget : K → J) (extraDegree : K → ℤ)
  (extraCoefficient : ∀ k, GradedHom R (value (extraSource k)) (value (extraTarget k)) (extraDegree k))

abbrev DGCodeAugmentedCoefficientIndex : Type u := DGCodeHomGeneratorIndex R κ c ⊕ K

lemma dgCodeAugmentedCoefficientIndex_cardinal_le (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ) :
    Cardinal.mk (DGCodeAugmentedCoefficientIndex R κ c (K := K)) ≤ κ := by
  simp only [DGCodeAugmentedCoefficientIndex, Cardinal.mk_sum, Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ (dgCodeHomGeneratorIndex_cardinal_le R κ c hκ) hK

def dgCodeAugmentedSource : DGCodeAugmentedCoefficientIndex R κ c (K := K) → J :=
  Sum.elim (dgCodeGeneratorSource R κ c D value F) extraSource

def dgCodeAugmentedTarget : DGCodeAugmentedCoefficientIndex R κ c (K := K) → J :=
  Sum.elim (dgCodeGeneratorTarget R κ c D value F) extraTarget

def dgCodeAugmentedDegree : DGCodeAugmentedCoefficientIndex R κ c (K := K) → ℤ :=
  Sum.elim (dgCodeGeneratorDegree R κ c) extraDegree

def dgCodeAugmentedCoefficient (i : DGCodeAugmentedCoefficientIndex R κ c (K := K)) :
    GradedHom R (value (dgCodeAugmentedSource R κ c D value F extraSource i))
      (value (dgCodeAugmentedTarget R κ c D value F extraTarget i))
      (dgCodeAugmentedDegree R κ c extraDegree i) :=
  match i with
  | .inl j => dgCodeGeneratorCoefficient R κ c D value F j
  | .inr k => extraCoefficient k

lemma dgCodeAugmentedImage_contains :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan
        (dgCodeAugmentedSource R κ c D value F extraSource)
        (dgCodeAugmentedTarget R κ c D value F extraTarget)
        (dgCodeAugmentedDegree R κ c extraDegree) R D value
        (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
        (F.obj x).label (F.obj y).label n := by
  apply generatedHomImage_of_codeGenerators R κ c _ _ _ D value _ F
  intro x y n b
  exact DGGeneratedHomWord.evaluate_mem_span _ _ _ R D value
    (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
    (.generator (.inl ⟨x, y, ULift.up n, b⟩))

lemma dgCodeAugmentedCoefficient_mem (k : K) :
    extraCoefficient k ∈ DGGeneratedHomWord.linearSpan
      (dgCodeAugmentedSource R κ c D value F extraSource)
      (dgCodeAugmentedTarget R κ c D value F extraTarget)
      (dgCodeAugmentedDegree R κ c extraDegree) R D value
      (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
      (extraSource k) (extraTarget k) (extraDegree k) := by
  have h := DGGeneratedHomWord.evaluate_mem_span
    (dgCodeAugmentedSource R κ c D value F extraSource)
    (dgCodeAugmentedTarget R κ c D value F extraTarget)
    (dgCodeAugmentedDegree R κ c extraDegree) R D value
    (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
    (.generator (Sum.inr k))
  exact h

end SerrePositivity.DifferentialGraded
end

end GeneratedHomAugmentedCoefficients

/-! ## GeneratedHomAugmentedCode（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomAugmentedCode.lean） -/

/-!
概要：追加κ個以下の斉次係数を含み、元の出発 dg 関手を厳密に因子化するコードを構成する。
方針：元の全基底像と追加係数を併合し、κ自由被覆と全 Hom 同型による持ち上げを合成する。
規約：元の対象ラベルと全 Hom 作用を保持し、任意閉射の係数選択は別工程とする。
使われ方：c′ の共通出発提示の係数精密化。
-/

@[expose] public section GeneratedHomAugmentedCode
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (extraSource extraTarget : K → Set.Iio a) (extraDegree : K → ℤ)
  (extraCoefficient : ∀ k, GradedHom R (value (extraSource k)) (value (extraTarget k)) (extraDegree k))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

local notation "S" => dgCodeAugmentedSource R κ c D value F extraSource
local notation "T" => dgCodeAugmentedTarget R κ c D value F extraTarget
local notation "N" => dgCodeAugmentedDegree R κ c extraDegree
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F
  extraSource extraTarget extraDegree extraCoefficient
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgAugmentedSourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgAugmentedSourceCodeEvaluation : DGFunctor R
    ((dgAugmentedSourceCode R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgAugmentedSourceCodeInclusion : DGFunctor R (c.Objects R κ)
    ((dgAugmentedSourceCode R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).Objects R κ) :=
  DGGeneratedHomWord.codeFunctorLift R D κ a S T N value P hκ hB
    (c.Objects R κ) F
    (dgCodeAugmentedImage_contains R κ c D value F extraSource extraTarget extraDegree extraCoefficient)

lemma dgAugmentedSourceCodeInclusion_comp_evaluation :
    (dgAugmentedSourceCodeInclusion R κ c a D value F extraSource extraTarget extraDegree
      extraCoefficient hκ hK).comp
      (dgAugmentedSourceCodeEvaluation R κ c a D value F extraSource extraTarget extraDegree
        extraCoefficient hκ hK) = F.comp (dgObjectImageEvaluation R value) :=
  DGGeneratedHomWord.codeFunctorLift_comp_evaluation R D κ a S T N value P hκ hB
    (c.Objects R κ) F
    (dgCodeAugmentedImage_contains R κ c D value F extraSource extraTarget extraDegree extraCoefficient)

end SerrePositivity.DifferentialGraded
end

end GeneratedHomAugmentedCode

/-! ## GeneratedHomAugmentedClosedFamily（旧 SerrePositivity/DifferentialGraded/Presentation/GeneratedHomAugmentedClosedFamily.lean） -/

/-!
概要：κ個以下の元の閉射を同じ精密化コードへ同時に持ち上げる。
方針：各閉射の零 cycle を追加係数に取り、コードの閉射回収を適用する。
規約：元の dg 関手の全 Hom と、指定閉射の実評価を厳密に保持する。
使われ方：c′ の係数精密化の閉射族版。任意加群閉射の係数選択は別途必要。
-/

@[expose] public section GeneratedHomAugmentedClosedFamily
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (D : Type v) [DGCategory R D] (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (source target : K → Set.Iio a)
  (f : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
    ForgetEnrichment.of (Complex R) (value (target k)))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

def dgClosedFamilyCoefficient (k : K) : GradedHom R (value (source k)) (value (target k)) 0 :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f k))).val

local notation "S" => dgCodeAugmentedSource R κ c D value F source
local notation "T" => dgCodeAugmentedTarget R κ c D value F target
local notation "N" => dgCodeAugmentedDegree R κ c (fun _ : K => (0 : ℤ))
local notation "P" => dgCodeAugmentedCoefficient R κ c D value F source target
  (fun _ : K => (0 : ℤ)) (dgClosedFamilyCoefficient R κ a D value source target f)
local notation "hB" => dgCodeAugmentedCoefficientIndex_cardinal_le R κ c hκ hK

def dgClosedFamilySourceCode : DGCategoryPresentationCode R κ :=
  DGGeneratedHomWord.code R D κ a S T N value P hκ hB

def dgClosedFamilySourceEvaluation : DGFunctor R
    ((dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ) D :=
  DGGeneratedHomWord.codeEvaluation R D κ a S T N value P hκ hB

def dgClosedFamilySourceInclusion : DGFunctor R (c.Objects R κ)
    ((dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ) :=
  dgAugmentedSourceCodeInclusion R κ c a D value F source target (fun _ : K => 0)
    (dgClosedFamilyCoefficient R κ a D value source target f) hκ hK

lemma dgClosedFamilySourceInclusion_comp_evaluation :
    (dgClosedFamilySourceInclusion R κ c a D value F source target f hκ hK).comp
      (dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK) =
    F.comp (dgObjectImageEvaluation R value) :=
  dgAugmentedSourceCodeInclusion_comp_evaluation R κ c a D value F source target
    (fun _ : K => 0) (dgClosedFamilyCoefficient R κ a D value source target f) hκ hK

def dgClosedFamilySourceArrow (k : K) :
    ForgetEnrichment.of (Complex R)
      (show (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ
        from source k) ⟶
    ForgetEnrichment.of (Complex R)
      (show (dgClosedFamilySourceCode R κ c a D value F source target f hκ hK).Objects R κ
        from target k) :=
  DGGeneratedHomWord.codeClosedLift R D κ a S T N value P hκ hB (source k) (target k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun _ : K => 0)
      (dgClosedFamilyCoefficient R κ a D value source target f) k)

lemma dgClosedFamilySourceArrow_map (k : K) :
    (dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK).onClosed.map
      (dgClosedFamilySourceArrow R κ c a D value F source target f hκ hK k) = f k :=
  DGGeneratedHomWord.codeClosedLift_map R D κ a S T N value P hκ hB (source k) (target k) (f k)
    (dgCodeAugmentedCoefficient_mem R κ c D value F source target (fun _ : K => 0)
      (dgClosedFamilyCoefficient R κ a D value source target f) k)

end SerrePositivity.DifferentialGraded
end

end GeneratedHomAugmentedClosedFamily
