module

public import SerrePositivity.KST.DerivedGeometry.AffineQuasicoherentCech
public import SerrePositivity.KST.DerivedGeometry.SheafCechAugmentation

/-!
概要：アフィン準連接層の有限基本開 Čech 増大は準同型。
方針：零次数の層条件と全正次数の局所化による完全性を合わせる。
規約：切断の単一項複体から実際の Čech 複体への増大を用いる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}}

/--
概要：有限基本開被覆の Čech 増大はアフィン準連接層の切断を準同型で分解する。
方針：零次数は層条件、正次数は局所化と収縮から得た完全性を使う。
規約：全次数の準同型性を証明し、途中で複体を切断しない。
使われ方：TT §3、Toën §3.2 のアフィン Čech 分解。
-/
lemma affineQuasicoherentCechAugmentation_quasiIso (N : (Spec R).Modules)
    [N.IsQuasicoherent] {ι : Type u} [Finite ι] (f : ι → R)
    (hcover : (⨆ i, basicOpen (f i)) = ⊤) :
    QuasiIso (sheafCechAugmentation (modulesSpecToSheaf.obj N) (fun i => basicOpen (f i))) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => infer_instance
  | succ n =>
    apply (quasiIsoAt_iff_exactAt _ (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ n)).mpr
    exact affineQuasicoherentCech_exactAt N f hcover n

/--
概要：アフィン準連接係数加群層も基礎切断の Čech 増大が準同型。
方針：基礎 O 加群層の準連接性を使って前の定理を適用する。
規約：非可換係数 H に平坦性を仮定しない。
使われ方：TT §3、Toën §3.2 の係数版アフィン Čech 分解。
-/
lemma affineCoefficientCechAugmentation_quasiIso (H : Type u) [Ring H] [Algebra R H]
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    {ι : Type u} [Finite ι] (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = ⊤) :
    QuasiIso (sheafCechAugmentation
      (modulesSpecToSheaf.obj
        ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N.obj))
      (fun i => basicOpen (f i))) := by
  let : ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj
    N.obj).IsQuasicoherent := N.property
  exact affineQuasicoherentCechAugmentation_quasiIso _ f hcover

end SerrePositivity.KST.DerivedGeometry
