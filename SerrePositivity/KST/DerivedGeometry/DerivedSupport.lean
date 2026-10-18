module

public import SerrePositivity.KST.DerivedGeometry.DqcRestriction
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
概要：開部分の補集合に台を持つ条件を実際の導来制限の核として同定する。
方針：全次数のコホモロジーによる零対象判定と導来制限の比較を使う。
規約：局所化同値や台つき compact 生成はここでは仮定しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1、Toën §3.2 の T2。
-/

@[expose] public section
noncomputable section
universe u v w w'
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：非有界導来対象は全コホモロジーが零のとき、かつそのときに限り零。
方針：零自己射にコホモロジーによる同型判定を適用する。
規約：実際の Mathlib 導来圏を使う。
使われ方：Neeman 1992 Thm 2.1、TT 3.19 の台つき対象。
-/
lemma derivedObject_isZero_iff_homology {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : DerivedCategory C) :
    IsZero M ↔ ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj M) := by
  constructor
  · intro h n
    exact (DerivedCategory.homologyFunctor C n).map_isZero h
  · intro h
    have : IsIso (0 : M ⟶ M) := (DerivedCategory.isIso_iff C _).mpr (fun n => by
      rw [Functor.map_zero, ← (h n).eq_zero_of_src (𝟙 _)]
      infer_instance)
    exact IsZero.of_epi_zero M M

namespace CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)
  [HasDerivedCategory.{w} B.Modules]

/--
概要：開部分の補集合に台を持つ導来係数加群層の対象条件。
方針：全コホモロジー層の開制限が零であると要求する。
規約：係数加群層の実際のコホモロジーを使い、有界性は不要。
使われ方：TT 3.19・8.1、Neeman 1992 Thm 2.1 の D_Z。
-/
def supportedOnComplement : ObjectProperty (DerivedCategory B.Modules) :=
  fun M => ∀ n : ℤ, IsZero ((B.openRestriction U).obj
    ((DerivedCategory.homologyFunctor B.Modules n).obj M))

/--
概要：補集合に台を持つ条件は導来圏の同型で不変。
方針：コホモロジーの開制限が与える同型で零対象性を移す。
規約：開部分の導来圏の選択は不要。
使われ方：TT 3.19・8.1 の台つき充満部分圏。
-/
instance supportedOnComplement_closedUnderIso :
    (B.supportedOnComplement U).IsClosedUnderIsomorphisms where
  of_iso e h n :=
    (((B.openRestriction U).mapIso
      ((DerivedCategory.homologyFunctor B.Modules n).mapIso e)).isZero_iff).mp (h n)

/--
概要：準連接コホモロジーと補集合への台の条件を持つ実際の充満部分圏。
方針：元の導来圏内の二つの対象条件の共通部分を取る。
規約：Dqc の定義を置き換えず、その台つき部分を切り出す。
使われ方：TT 3.19・8.1、Neeman 1992 Thm 2.1 の D_qc,Z。
-/
abbrev DqcSupported := (B.hasQuasicoherentCohomology ⊓ B.supportedOnComplement U).FullSubcategory

variable [HasDerivedCategory.{w'} (B.restrict U).Modules]

/--
概要：補集合に台を持つ条件は導来開制限の像が零であることに一致する。
方針：全コホモロジーによる零対象判定を自然な制限比較で移す。
規約：冪等完備化や別の導来対象の選択を加えない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の局所化の核。
-/
lemma supportedOnComplement_iff (M : DerivedCategory B.Modules) :
    B.supportedOnComplement U M ↔ IsZero ((B.derivedRestriction U).obj M) := by
  rw [derivedObject_isZero_iff_homology]
  constructor
  · intro h n
    exact ((B.derivedRestrictionHomologyIso U n).app M).isZero_iff.mpr (h n)
  · intro h n
    exact ((B.derivedRestrictionHomologyIso U n).app M).isZero_iff.mp (h n)

/--
概要：コホモロジーで定義した台つき条件は導来制限関手の核と同じ対象条件。
方針：全対象について証明済みの同値を適用する。
規約：核を別の抽象的な対象条件として仮定しない。
使われ方：Neeman 1992 Thm 2.1、TT 3.19・8.1 の局所化の接続点。
-/
theorem supportedOnComplement_eq_kernel :
    B.supportedOnComplement U = (B.derivedRestriction U).kernel := by
  ext M
  exact B.supportedOnComplement_iff U M

end CoefficientSheaf
end SerrePositivity.KST.DerivedGeometry
