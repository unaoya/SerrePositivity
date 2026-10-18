module

public import SerrePositivity.KST.DerivedGeometry.DerivedForget

/-!
# 準連接コホモロジーを持つ部分圏への導来忘却の制限

概要：係数つき D_qc の対象条件を、導来忘却の像の準連接性として同定する。
方針：導来忘却とコホモロジーの自然同型を使う。
規約：D(QCoh) との同値は用いない。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w w'

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable (X : Scheme.{u}) [HasDerivedCategory.{w'} X.Modules]

/--
概要：構造層の導来圏における準連接コホモロジー条件。
方針：全次数のコホモロジー層の準連接性を要求する。
規約：複体の各項の準連接性は要求しない。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1 の D_qc(X)。
-/
def quasicoherentCohomology : ObjectProperty (DerivedCategory X.Modules) :=
  fun M => ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj M).IsQuasicoherent

/--
概要：通常の D_qc(X) を実際の加群層の導来圏の充満部分圏として定義する。
方針：コホモロジーの準連接性で切り出す。
規約：準連接層のアーベル圏を先に導来化した圏とは区別する。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1 の係数忘却先。
-/
abbrev DqcO := (quasicoherentCohomology X).FullSubcategory

namespace CoefficientSheaf

variable {X} (B : CoefficientSheaf X) [HasDerivedCategory.{w} B.Modules]

/--
概要：係数つき対象が D_qc に属する条件は、導来忘却の像が D_qc(X) に属する条件に等しい。
方針：各コホモロジー層の自然同型で準連接性を移す。
規約：有界性・平坦性・分離性は要求しない。
使われ方：KST D4・T1、Toën §3.2 の生成と降下の対象条件。
-/
lemma hasQuasicoherentCohomology_iff (M : DerivedCategory B.Modules) :
    B.hasQuasicoherentCohomology M ↔
      quasicoherentCohomology X (B.derivedForget.obj M) := by
  constructor
  · intro h n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((B.derivedForgetHomologyIso n).app M).symm (h n)
  · intro h n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((B.derivedForgetHomologyIso n).app M) (h n)

/--
概要：係数つき D_qc から構造層の D_qc への忘却関手。
方針：導来忘却をコホモロジーの準連接性の部分圏へ制限する。
規約：局所 perfect 性や compact 性の比較は別定理。
使われ方：KST T1、Toën §3.2 の係数つき compact 生成。
-/
def dqcForget : B.Dqc ⥤ DqcO X :=
  ObjectProperty.lift _ (B.dqcInclusion ⋙ B.derivedForget)
    (fun M => (B.hasQuasicoherentCohomology_iff M.obj).mp M.property)

/--
概要：D_qc に制限した係数忘却も同型を反映する。
方針：充満部分圏の包含と、導来忘却の同型反映性を使う。
規約：導来忘却の忠実性は主張しない。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の生成判定の係数版。
-/
instance dqcForget_reflectsIsomorphisms : B.dqcForget.ReflectsIsomorphisms := by
  have : B.dqcInclusion.ReflectsIsomorphisms :=
    inferInstanceAs (B.hasQuasicoherentCohomology.ι.ReflectsIsomorphisms)
  have : (B.dqcForget ⋙ (quasicoherentCohomology X).ι).ReflectsIsomorphisms :=
    inferInstanceAs ((B.dqcInclusion ⋙ B.derivedForget).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp B.dqcForget (quasicoherentCohomology X).ι

end CoefficientSheaf

end SerrePositivity.KST.DerivedGeometry
