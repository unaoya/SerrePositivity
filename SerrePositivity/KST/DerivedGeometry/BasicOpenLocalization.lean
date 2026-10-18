module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：基本開被覆に沿う局所化で加群の同型と複体の完全性を検出する。
方針：被覆を単位イデアル生成に直し、局所化加群の完全性の局所判定を使う。
規約：複体の有界性や加群の有限生成性は不要。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [CommRing R] (s : Set R)
  (hcover : (⨆ r : s, PrimeSpectrum.basicOpen r.val) = ⊤)

include hcover

/--
概要：基本開被覆の定義元は単位イデアルを生成する。
方針：基本開の和集合とイデアルの零点集合の比較を使う。
規約：空のスペクトルと空の被覆も含む。
使われ方：TT §3、Toën §3.2 の Čech 複体の局所判定。
-/
lemma basicOpenCover_span : Ideal.span s = ⊤ := by
  simpa only [Subtype.range_val] using PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover

/--
概要：基本開被覆の局所化加群関手は同時に同型を反映する。
方針：単位イデアルを生成する族での局所化の全単射判定を使う。
規約：各局所化の標的は対応する局所化環の加群圏。
使われ方：TT §3、Toën §3.2 のアフィン Čech 比較。
-/
lemma basicOpenLocalized_isIso_iff {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    IsIso f ↔ ∀ r : s, IsIso ((ModuleCat.localizedModuleFunctor (.powers r.val)).map f) := by
  constructor
  · intro h r
    exact Functor.map_isIso _ f
  · intro h
    apply (ConcreteCategory.isIso_iff_bijective f).mpr
    apply bijective_of_isLocalized_span s (basicOpenCover_span s hcover)
      (fun r : s => M.localizedModule (.powers r.val))
      (fun r => M.localizedModuleMkLinearMap (.powers r.val))
      (fun r : s => N.localizedModule (.powers r.val))
      (fun r => N.localizedModuleMkLinearMap (.powers r.val)) f.hom
    intro r
    exact (ConcreteCategory.isIso_iff_bijective
      ((ModuleCat.localizedModuleFunctor (.powers r.val)).map f)).mp (h r)

/--
概要：加群の短複体の完全性は基本開被覆上の局所化で判定できる。
方針：局所化の完全性と単位イデアル生成族による完全性の反映を使う。
規約：被覆や加群に有限性の仮定を要求しない。
使われ方：TT §3、Toën §3.2 の Čech 複体の完全性。
-/
lemma basicOpenLocalized_exact_iff (T : ShortComplex (ModuleCat.{u} R)) :
    T.Exact ↔ ∀ r : s, (T.map (ModuleCat.localizedModuleFunctor (.powers r.val))).Exact := by
  constructor
  · intro h r
    exact ModuleCat.localizedModuleFunctor_map_exact _ T h
  · intro h
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    apply exact_of_isLocalized_span s (basicOpenCover_span s hcover)
      (fun r : s => T.X₁.localizedModule (.powers r.val))
      (fun r => T.X₁.localizedModuleMkLinearMap (.powers r.val))
      (fun r : s => T.X₂.localizedModule (.powers r.val))
      (fun r => T.X₂.localizedModuleMkLinearMap (.powers r.val))
      (fun r : s => T.X₃.localizedModule (.powers r.val))
      (fun r => T.X₃.localizedModuleMkLinearMap (.powers r.val)) T.f.hom T.g.hom
    intro r
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h r)

/--
概要：任意の複体の各次数の完全性は基本開被覆上の局所化で判定できる。
方針：各次数に対応する短複体へ局所判定を適用する。
規約：整数添字に限らず任意の複体形状で述べる。
使われ方：TT §3、Toën §3.2 の非有界 Čech 比較。
-/
lemma basicOpenLocalized_exactAt_iff {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (n : ι) :
    K.ExactAt n ↔ ∀ r : s,
      ((ModuleCat.localizedModuleFunctor (.powers r.val)).mapHomologicalComplex c).obj K |>.ExactAt n :=
  basicOpenLocalized_exact_iff s hcover (K.sc n)

/--
概要：任意の複体の acyclic 性は基本開被覆上の局所化で判定できる。
方針：各次数の完全性の判定を全次数について適用する。
規約：無限方向の複体にも同じ判定を使う。
使われ方：TT §3、Toën §3.2 の非有界アフィン計算。
-/
lemma basicOpenLocalized_acyclic_iff {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) :
    K.Acyclic ↔ ∀ r : s,
      (((ModuleCat.localizedModuleFunctor (.powers r.val)).mapHomologicalComplex c).obj K).Acyclic := by
  constructor
  · intro h r n
    exact (basicOpenLocalized_exactAt_iff s hcover K n).mp (h n) r
  · intro h n
    exact (basicOpenLocalized_exactAt_iff s hcover K n).mpr (fun r => h r n)

/--
概要：複体の準同型は基本開被覆上の局所化で保存かつ検出される。
方針：局所化のコホモロジー比較と加群の同型の局所判定を使う。
規約：任意の複体形状・全次数について判定する。
使われ方：TT §3、Toën §3.2 の Čech 比較の準同型判定。
-/
lemma basicOpenLocalized_quasiIso_iff {ι : Type v} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ r : s, QuasiIso
      (((ModuleCat.localizedModuleFunctor (.powers r.val)).mapHomologicalComplex c).map f) := by
  constructor
  · intro h r
    let := h
    infer_instance
  · intro h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    apply (basicOpenLocalized_isIso_iff s hcover _).mpr
    intro r
    let F := ModuleCat.localizedModuleFunctor (.powers r.val)
    let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) c n).map f
    let : QuasiIso ((F.mapHomologicalComplex c).map f) := h r
    have hi : IsIso ((F.mapShortComplex ⋙ ShortComplex.homologyFunctor _).map φ) := by
      change IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map f) n)
      infer_instance
    exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso F) φ).mp hi

end SerrePositivity.KST.DerivedGeometry
