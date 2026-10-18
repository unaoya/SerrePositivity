module

public import SerrePositivity.KST.DerivedGeometry.RingedFreeYoneda
public import SerrePositivity.KST.DerivedGeometry.ReflectiveColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules

/-!
概要：任意の環層の加群層から基礎アーベル群層への忘却の完全性。
方針：加群層化と基礎層化の比較を反射的局所化の余極限保存へ適用する。
規約：係数環層の平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech の完全性反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：任意の環層上の加群層から基礎アーベル群層への忘却は小さい余極限を保つ。
方針：加群層化の随伴と基礎層化との比較から反射的余極限判定を適用する。
規約：添字の宇宙は u 以下であり、係数の可換性も平坦性も不要。
使われ方：TT §3、Toën §3.2 の環層版の自由 Čech 分解。
-/
lemma ringedToSheaf_preservesColimits :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
  refine ⟨fun {J} _ => ?_⟩
  let L := PresheafOfModules.sheafification.{u} (𝟙 B.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 B.obj)
  have : PreservesColimitsOfShape J (L ⋙ SheafOfModules.toSheaf B) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 B.obj)).symm
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  exact preservesColimitsOfShape_of_reflective _ _ adj _

/--
概要：環層上の加群層の短複体は基礎アーベル群層で完全性を判定できる。
方針：忠実で完全な基礎層への忘却による完全性の保存と反映を使う。
規約：切断での大域完全性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由増大 Čech。
-/
lemma ringed_exact_iff_toSheaf (S : ShortComplex (SheafOfModules.{u} B)) :
    S.Exact ↔ (S.map (SheafOfModules.toSheaf B)).Exact := by
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) :=
    ringedToSheaf_preservesColimits X B
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} B) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact (S.exact_map_iff_of_faithful (SheafOfModules.toSheaf B)).symm

end SerrePositivity.KST.DerivedGeometry
