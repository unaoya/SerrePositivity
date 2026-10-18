module

public import SerrePositivity.KST.DerivedGeometry.AffineCechExact
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeFunctor

/-!
概要：アフィン準連接係数加群層の有限基本開 Čech 完全性。
方針：tilde の実際の余単位によって既証の Čech 完全性を移す。
規約：係数 H は非可換でもよく、平坦性も仮定しない。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の係数版計算。
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
概要：任意のアフィン準連接 O 加群層の Čech 複体は全正次数で完全。
方針：大域切断の tilde からの余単位の同型を Čech 関手に適用する。
規約：各項は元の層の実際の切断。
使われ方：TT §3、Toën §3.2 のアフィン非有界導来比較の入力。
-/
lemma affineQuasicoherentCech_exactAt (N : (Spec R).Modules) [N.IsQuasicoherent]
    {ι : Type u} [Finite ι] (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = ⊤)
    (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj N).obj).ExactAt (n + 1) := by
  let e := (cechComplexFunctor (fun i => basicOpen (f i))).mapIso
    ((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _).mapIso (asIso N.fromTildeΓ))
  exact (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mp
    (affineCech_exactAt (moduleSpecΓFunctor.obj N) f hcover n)

/--
概要：アフィン準連接 H 係数加群層の基礎 Čech 複体は全正次数で完全。
方針：係数を忘れた準連接 O 加群層へ前の定理を適用する。
規約：H の可換性・平坦性を要求しない。
使われ方：TT §3、Toën §3.2 の係数版アフィン導来比較の入力。
-/
lemma affineCoefficientCech_exactAt (H : Type u) [Ring H] [Algebra R H]
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    {ι : Type u} [Finite ι] (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = ⊤)
    (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj
        ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N.obj)).obj).ExactAt
          (n + 1) := by
  let : ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj
    N.obj).IsQuasicoherent := N.property
  exact affineQuasicoherentCech_exactAt _ f hcover n

end SerrePositivity.KST.DerivedGeometry
