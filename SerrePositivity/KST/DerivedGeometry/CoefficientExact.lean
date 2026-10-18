module

public import SerrePositivity.KST.DerivedGeometry.CoefficientForget
public import SerrePositivity.KST.DerivedGeometry.ReflectiveColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# 係数忘却の完全性と余極限保存

概要：係数を忘れる関手が有限極限・有限余極限と小さい余極限を保つことを証明する。
方針：加群前層の余極限を層化し、基礎アーベル群の層へ忘れる関手で検証する。
規約：平坦性や各項の準連接性を要求しない。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

/-- 概要：層の加群の圏構造を明示する。方針：Mathlib の構造を再利用する。
規約：このファイル内の推論だけに使う。使われ方：Toën §3.2 の層化の比較。 -/
local instance {X : Scheme.{u}} (R : TopCat.Sheaf RingCat.{u} X) :
    Category.{u} (SheafOfModules.{u} R) := SheafOfModules.instCategory

/-- 概要：前層の加群の圏構造を明示する。方針：Mathlib の構造を再利用する。
規約：このファイル内の推論だけに使う。使われ方：Toën §3.2 の層化前の余極限。 -/
local instance {X : Scheme.{u}} (R : TopCat.Sheaf RingCat.{u} X) :
    Category.{u} (PresheafOfModules.{u} R.obj) := PresheafOfModules.instCategory

/--
概要：加群層から基礎アーベル群の層への忘却は小さい余極限を保つ。
方針：前層からの層化の前に合成し、反射的局所化の余極限判定を使う。
規約：余極限の添字の宇宙は加群の宇宙以下とする。
使われ方：Toën §3.2、KST T1 の係数忘却の余極限保存。
-/
lemma toSheaf_preservesColimits {X : Scheme.{u}} (R : TopCat.Sheaf RingCat.{u} X) :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) := by
  refine ⟨fun {J} _ => ?_⟩
  let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  have : PreservesColimitsOfShape J (L ⋙ SheafOfModules.toSheaf R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  have : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  exact preservesColimitsOfShape_of_reflective _ _ adj _

namespace CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数忘却は有限極限を保つ。
方針：基礎アーベル群の層への忘却が有限極限を保存・反映することを使う。
規約：任意の係数環層について成り立ち、平坦性は不要。
使われ方：Toën §3.2、KST T1 の完全な忘却関手の左完全性。
-/
instance forget_preservesFiniteLimits : PreservesFiniteLimits B.forget := by
  let G := SheafOfModules.restrictScalars.{u} B.structureMap
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : ReflectsFiniteLimits F :=
    PresheafOfModules.instReflectsFiniteLimitsSheafOfModulesSheafAddCommGrpCatToSheaf
  have : PreservesFiniteLimits (G ⋙ F) :=
    SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf B.ring
  exact preservesFiniteLimits_of_reflects_of_preserves G F

/--
概要：係数忘却は小さい余極限を保つ。
方針：基礎アーベル群の層への忘却で余極限を判定する。
規約：層化後の余極限を使い、開ごとの切断での計算とは同一視しない。
使われ方：Toën §3.2、KST T1 の自由・忘却随伴を介する compact 性の移送。
-/
instance forget_preservesColimits : PreservesColimitsOfSize.{u, u} B.forget := by
  let G := SheafOfModules.restrictScalars.{u} B.structureMap
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesColimitsOfSize.{u, u} F := toSheaf_preservesColimits _
  have : F.ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have : ReflectsColimitsOfSize.{u, u} F := reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u} (G ⋙ F) := toSheaf_preservesColimits B.ring
  exact preservesColimits_of_reflects_of_preserves G F

/--
概要：係数忘却は有限余極限を保つ。
方針：小さい余極限の保存から有限の場合を取り出す。
規約：係数の平坦性は不要。
使われ方：KST T1、Toën §3.2 の忘却の完全性と導来忘却の構成。
-/
instance forget_preservesFiniteColimits : PreservesFiniteColimits B.forget :=
  PreservesColimitsOfSize.preservesFiniteColimits B.forget

end CoefficientSheaf

end SerrePositivity.KST.DerivedGeometry
