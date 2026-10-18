module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# 係数環層と準連接コホモロジーを持つ導来対象

概要：スキーム上の実際の環層と構造層からの射を用い、係数加群層の導来圏内で
準連接コホモロジーを持つ対象を定義する。
方針：層の圏と導来局所化には Mathlib の構成を使う。
規約：加群は左加群。係数環層の可換性・平坦性は仮定しない。
使われ方：KST 経路 D4、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の
幾何的係数層の共通の型。生成・局所化・降下定理はこの定義とは別に証明する。
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：スキーム上の係数環層と構造層からの環層射。
方針：環層そのものを保持し、加群圏を後から構成する。
規約：可換性・平坦性を要求しない。中心性は具体的係数の構成時に検証する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数加群層の基礎データ。
-/
structure CoefficientSheaf (X : Scheme.{u}) where
  /-- 概要：係数の環層。方針：環の層を使う。規約：非可換を許す。
  使われ方：Toën §3.2 の加群層の係数。 -/
  ring : TopCat.Sheaf RingCat.{u} X
  /-- 概要：構造層の作用。方針：環層射で指定する。規約：単位を保つ。
  使われ方：Toën §3.2 の係数忘却。 -/
  structureMap : X.ringCatSheaf ⟶ ring

namespace CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数環層の左加群層の圏。
方針：Mathlib の `SheafOfModules` を用いる。
規約：加群の宇宙をスキームの宇宙に合わせる。
使われ方：Toën §3.2 の非有界複体とその導来圏の入力。
-/
abbrev Modules := SheafOfModules.{u} B.ring

/-- 概要：係数加群層の圏構造。方針：層の標準構造を明示する。
規約：射の宇宙は u。使われ方：Toën §3.2 の導来圏の入力。 -/
instance modulesCategory : Category.{u} B.Modules := SheafOfModules.instCategory

/-- 概要：係数加群層はアーベル圏。方針：層の標準構造を使う。
規約：非可換係数を許す。使われ方：Toën §3.2 のコホモロジー。 -/
instance modulesAbelian : Abelian B.Modules :=
  SheafOfModules.instAbelian B.ring

/--
概要：係数作用を忘れて構造層の加群層を取る関手。
方針：環層射に沿うスカラー制限を使う。
規約：自由・忘却随伴の右側の層レベルの関手。
使われ方：Bondal–van den Bergh Thm 3.1.1 の係数版 T1 の準連接性条件。
-/
def forget : B.Modules ⥤ X.Modules :=
  SheafOfModules.restrictScalars B.structureMap

/--
概要：係数忘却は射の加法を保つ。
方針：スカラー制限の加法性を使う。
規約：係数環の平坦性を要求しない。
使われ方：Toën §3.2 の複体への忘却の持ち上げ。
-/
instance forget_additive : B.forget.Additive :=
  SheafOfModules.instAdditiveRestrictScalars B.structureMap

variable [HasDerivedCategory.{w} B.Modules]

/--
概要：係数加群層の非有界導来圏のコホモロジーを構造層上で取る関手。
方針：導来コホモロジーの後に係数を忘れる。
規約：導来忘却関手の存在や完全性をこの定義で仮定しない。
使われ方：KST D4、Toën §3.2 の D_qc の対象条件。
-/
def underlyingCohomology (n : ℤ) : DerivedCategory B.Modules ⥤ X.Modules :=
  DerivedCategory.homologyFunctor B.Modules n ⋙ B.forget

/--
概要：忘却した全コホモロジー層が準連接であるという性質。
方針：準連接性を各コホモロジー層について要求する。
規約：複体の各項の準連接性とは区別する。
使われ方：KST D4、Toën §3.2 の D_qc(X;H) の定義。
-/
def hasQuasicoherentCohomology : ObjectProperty (DerivedCategory B.Modules) :=
  fun M => ∀ n : ℤ, ((B.underlyingCohomology n).obj M).IsQuasicoherent

/--
概要：準連接コホモロジーを持つ条件は導来同型で不変。
方針：コホモロジー関手で同型を送り、層の準連接性の同型不変性を使う。
規約：生成・降下定理を仮定しない。
使われ方：KST D4、Toën §3.2 の D_qc の充満部分圏と比較関手。
-/
instance hasQuasicoherentCohomology_closedUnderIso :
    B.hasQuasicoherentCohomology.IsClosedUnderIsomorphisms where
  of_iso e h n :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((B.underlyingCohomology n).mapIso e) (h n)

/--
概要：係数加群層の導来圏内の準連接コホモロジーの充満部分圏。
方針：実際の導来対象に準連接性の証明を添える。
規約：有限アフィン降下模型との同値・compact 性は別定理。
使われ方：KST D4、Toën §3.2 の D_qc(X;H)。
-/
abbrev Dqc := B.hasQuasicoherentCohomology.FullSubcategory

/--
概要：D_qc から係数加群層の導来圏への包含。
方針：対象条件の充満部分圏の包含を使う。
規約：係数・宇宙の選択を変えない。
使われ方：KST D4、Neeman 1992 Thm 2.1 の局所化の比較先。
-/
def dqcInclusion : B.Dqc ⥤ DerivedCategory B.Modules :=
  B.hasQuasicoherentCohomology.ι

end CoefficientSheaf

end SerrePositivity.KST.DerivedGeometry
