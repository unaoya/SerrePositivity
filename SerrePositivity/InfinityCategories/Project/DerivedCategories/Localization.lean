module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.AcyclicVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportScalar
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportBasic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BaseChange
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import Mathlib.RingTheory.Flat.Localization
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion

/-! # 主開集合への局所化とコホモロジーの台

概要：V(a) 上の幾何学的支持は、局所化底変更の全ホモロジーが零となることと同値である。
方針：任意加群の台と局所化の零性の比較、平坦底変更によるホモロジー同型を使う。
規約：一般の複体に一様な冪消去を課さない。使われ方：D_Z を底変更の核として同定する基礎。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded TensorProduct
open scoped _root_.Simplicial
variable {S T : Type u} [CommRing S] [CommRing T]

/-- 概要：任意の加群の V(a) 上の台は、各元が a のある冪で消えることと同値である。
方針：Mathlib の局所化加群の零性による台の特徴づけを使う。
規約：冪は元に依存してよい。使われ方：一般の D_Z の台条件。 -/
lemma module_support_principal_iff_torsion (a : S) (M : ModuleCat.{u} S) :
    Module.support S M ⊆ supportZeroLocus (Ideal.span ({a} : Set S)) ↔
      Module.IsTorsion' M (Submonoid.powers a) := by
  change Module.support S M ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({a} : Set S) : Set S) ↔ _
  rw [PrimeSpectrum.zeroLocus_span]
  exact LocalizedModule.subsingleton_iff_support_subset.symm.trans
    (isTorsion'_iff_subsingleton_localizedModule (P := Submonoid.powers a) (M := M)).symm

variable [Algebra S T]

/-- 概要：任意の複体の V(a) 上の台は、局所化後の全ホモロジーの零性と同値である。
方針：局所化の平坦性とテンソル積による局所化加群を使う。
規約：T は S[1/a] の任意のモデル。使われ方：底変更の核の一般的な判定。 -/
theorem homologySupport_iff_localization_acyclic (a : S) [IsLocalization.Away a T]
    (P : Complex S) :
    HasHomologySupportOn (supportZeroLocus (Ideal.span ({a} : Set S))) P ↔
      ∀ i : ℤ, IsZero (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange (algebraMap S T)).obj P).homology i) := by
  have : Module.Flat S T := IsLocalization.flat T (Submonoid.powers a)
  constructor
  · intro h i
    have ht := (module_support_principal_iff_torsion a (P.homology i)).1 (h i)
    have hs := (isTorsion'_iff_subsingleton_tensor (P := Submonoid.powers a)
      (M := P.homology i) T).1 ht
    have : Subsingleton (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange (algebraMap S T)).obj P).homology i) :=
      (flatBaseChangeHomologyEquiv S T P i).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · intro h i
    have : Subsingleton (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange (algebraMap S T)).obj P).homology i) :=
      ModuleCat.subsingleton_of_isZero (h i)
    have ht : Subsingleton (T ⊗[S] P.homology i) :=
      (flatBaseChangeHomologyEquiv S T P i).symm.injective.subsingleton
    exact (module_support_principal_iff_torsion a (P.homology i)).2
      ((isTorsion'_iff_subsingleton_tensor (P := Submonoid.powers a) (M := P.homology i) T).2 ht)

/-- 概要：D5c の底変更 ∞ 関手の頂点で局所化のホモロジー核を判定できる。
方針：D5c の頂点計算式を複体の局所化判定に代入する。
規約：元の semifree 複体をそのまま使う。使われ方：D_Z と底変更 ∞ 関手の整合。 -/
theorem derivedSupport_iff_baseChange_homology_zero (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S (supportZeroLocus (Ideal.span ({a} : Set S))) (x.obj 0) ↔
      ∀ i : ℤ, IsZero
        ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (algebraMap S T)).app _ x).obj 0).val.homology i) :=
  homologySupport_iff_localization_acyclic (T := T) a (x.obj 0).val

/-- 概要：一般の D_Z(S) は D5c の局所化底変更の核である。
方針：全ホモロジーの局所化の零性と semifree 頂点の零性の判定を合成する。
規約：Z=V(a)、非有界複体も含み、一様な冪消去は要求しない。
使われ方：局所化列の台つき部分圏の判定。 -/
theorem derivedSupport_iff_baseChange_isZero (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S (supportZeroLocus (Ideal.span ({a} : Set S))) (x.obj 0) ↔
      IsZero (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (algebraMap S T)).app _ x⟩ :
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory T) :=
  (derivedSupport_iff_baseChange_homology_zero (T := T) a x).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityVertex_isZero_iff_homology T _).symm

/-- 概要：完全対象では幾何学的台・局所化底変更の零性・scalarSupported が一致する。
方針：一般の局所化核の判定と有限射影代表によるスカラー台の比較を組み合わせる。
規約：スカラー台との同値には完全性の仮定を保持する。使われ方：Perf_Z の三条件の比較。 -/
theorem perfectSupport_localization_scalar (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S (x.obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S (supportZeroLocus (Ideal.span ({a} : Set S))) (x.obj 0) ↔
      IsZero (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (algebraMap S T)).app _ x⟩ :
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory T)) ∧
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S (supportZeroLocus (Ideal.span ({a} : Set S))) (x.obj 0) ↔
      scalarSupported (fun _ : Fin 1 => a)
        ((HomotopyCategory.quotient _ _).obj (x.obj 0).val)) := by
  refine ⟨derivedSupport_iff_baseChange_isZero (T := T) a x, ?_⟩
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectModel_support_iff_scalar (fun _ : Fin 1 => a) (x.obj 0).val hx
  simpa only [Set.range_const, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty] using h

/-- 概要：D_Z の任意の頂点は局所化底変更で零対象になる。
方針：部分型の台条件に一般の核の判定を適用する。
規約：Z=V(a)。使われ方：D5c の ∞ 関手が台つき部分を消すこと。 -/
theorem derivedSupportCategory_baseChange_zero (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S (supportZeroLocus (Ideal.span ({a} : Set S)))) _⦋0⦌) :
    IsZero (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (algebraMap S T)).app _ x.val⟩ :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory T) :=
  (derivedSupport_iff_baseChange_isZero (T := T) a x.val).1 (x.property 0)

/-- 概要：Perf_Z の任意の頂点は局所化底変更で零対象になる。
方針：完全性と台の交わりから台条件を取り出す。
規約：K 理論側が必要とする完全対象の場合。使われ方：L4 の局所化の零化条件。 -/
theorem perfectSupportCategory_baseChange_zero (a : S) [IsLocalization.Away a T]
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S (supportZeroLocus (Ideal.span ({a} : Set S)))) _⦋0⦌) :
    IsZero (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (algebraMap S T)).app _ x.val⟩ :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory T) :=
  (derivedSupport_iff_baseChange_isZero (T := T) a x.val).1 (x.property 0).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories
