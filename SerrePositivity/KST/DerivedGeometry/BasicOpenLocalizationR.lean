module

public import SerrePositivity.KST.DerivedGeometry.BasicOpenLocalization
public import SerrePositivity.KST.DerivedGeometry.ModuleLocalizationR

/-!
概要：R 加群値の局所化による基本開被覆上の完全性判定。
方針：単位イデアル生成と局所化加群の完全性の局所判定を使う。
規約：複体の有界性・加群の有限性は要求しない。
使われ方：TT §3、Toën §3.2 の Čech 完全性の局所判定。
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
概要：加群の短複体の完全性は基本開被覆上の局所化で判定できる。
方針：局所化の完全性と単位イデアル生成族による完全性の反映を使う。
規約：被覆や加群に有限性の仮定を要求しない。
使われ方：TT §3、Toën §3.2 の Čech 複体の完全性。
-/
lemma basicOpenLocalizationR_exact_iff (T : ShortComplex (ModuleCat.{u} R)) :
    T.Exact ↔ ∀ r : s, (T.map (moduleLocalizationR (.powers r.val))).Exact := by
  constructor
  · intro h r
    exact moduleLocalizationR_map_exact _ T h
  · intro h
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    apply exact_of_isLocalized_span s (basicOpenCover_span s hcover)
      (fun r : s => LocalizedModule (.powers r.val) T.X₁)
      (fun r => LocalizedModule.mkLinearMap (.powers r.val) T.X₁)
      (fun r : s => LocalizedModule (.powers r.val) T.X₂)
      (fun r => LocalizedModule.mkLinearMap (.powers r.val) T.X₂)
      (fun r : s => LocalizedModule (.powers r.val) T.X₃)
      (fun r => LocalizedModule.mkLinearMap (.powers r.val) T.X₃) T.f.hom T.g.hom
    intro r
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h r)

/--
概要：任意の複体の各次数の完全性は基本開被覆上の局所化で判定できる。
方針：各次数に対応する短複体へ局所判定を適用する。
規約：整数添字に限らず任意の複体形状で述べる。
使われ方：TT §3、Toën §3.2 の非有界 Čech 比較。
-/
lemma basicOpenLocalizationR_exactAt_iff {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (n : ι) :
    K.ExactAt n ↔ ∀ r : s,
      ((moduleLocalizationR (.powers r.val)).mapHomologicalComplex c).obj K |>.ExactAt n :=
  basicOpenLocalizationR_exact_iff s hcover (K.sc n)

end SerrePositivity.KST.DerivedGeometry
