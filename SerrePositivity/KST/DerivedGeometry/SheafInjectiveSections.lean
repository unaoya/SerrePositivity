module

public import SerrePositivity.KST.DerivedGeometry.AffineLocalVanishing
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
概要：加群層の実際の injective 分解と右導来切断の比較。
方針：Grothendieck 性から十分な injective を得て Mathlib の分解を構成する。
規約：分解の存在・完全性・導来比較を未証明のフィールドにしない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン層コホモロジー。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [Ring R] {X : TopCat.{u}}

/--
概要：加群層の injective 分解を実際に構成する。
方針：Grothendieck アーベル圏に十分な injective がある定理を経て標準の分解を使う。
規約：分解の存在を入力として要求しない。
使われ方：TT §3、Toën §3.2 の右導来切断。
-/
def moduleSheafInjectiveResolution
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) : InjectiveResolution F :=
  InjectiveResolution.of F

/--
概要：選んだ injective 分解で計算する正次数の切断コホモロジー前層。
方針：分解の該当次数の短複体に切断コホモロジーを適用する。
規約：全ての開で同じ分解を用いる。
使われ方：TT §3、Toën §3.2 の Čech 比較の列。
-/
def injectiveSectionHomologyPresheaf
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ) :
    (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R :=
  sectionHomologyPresheaf ((moduleSheafInjectiveResolution F).cocomplex.sc (n + 1))

/--
概要：正次数の右導来切断は選んだ injective 分解の切断コホモロジーと同型。
方針：Mathlib の分解による右導来関手の計算定理を具体的な分解に適用する。
規約：比較の存在を新たな仮定にしない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の層コホモロジー。
-/
def moduleSheafRightDerivedSectionsIso
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (U : Opens X) (n : ℕ) :
    ((sheafModuleSections (R := R) U).rightDerived (n + 1)).obj F ≅
      (injectiveSectionHomologyPresheaf F n).obj (.op U) :=
  (moduleSheafInjectiveResolution F).isoRightDerivedObj (sheafModuleSections U) (n + 1)

/--
概要：injective 分解で計算する正次数のコホモロジーの各類は局所的に零。
方針：分解の正次数の完全性から切断コホモロジーの局所消滅を適用する。
規約：大域消滅とは区別する。
使われ方：TT §3、Toën §3.2 の Čech 比較の局所消滅。
-/
lemma injectiveSectionHomology_locallyZero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ)
    (U : Opens X) (z : (injectiveSectionHomologyPresheaf F n).obj (.op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      (injectiveSectionHomologyPresheaf F n).map (homOfLE hVU).op z = 0 :=
  sectionHomologyPresheaf_locallyZero _
    ((moduleSheafInjectiveResolution F).cocomplex_exactAt_succ n) U z x hx

/--
概要：アフィン準コンパクト開では正次数の分解コホモロジーの類は有限基本開上で零。
方針：分解の完全性と有限基本開への局所消滅の細分を使う。
規約：全ての被覆元に対する実際の制限写像を保持する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限 Čech 比較。
-/
lemma injectiveSectionHomology_finiteBasicOpenVanishing {A : Type u} [CommRing A]
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R)) (n : ℕ)
    (U : Opens (PrimeSpectrum A)) (hU : IsCompact (U : Set (PrimeSpectrum A)))
    (z : (injectiveSectionHomologyPresheaf (X := TopCat.of (PrimeSpectrum A)) F n).obj (.op U)) :
    ∃ (s : Finset U) (f : s → A) (hf : ∀ i, basicOpen (f i) ≤ U),
      (⨆ i, basicOpen (f i)) = U ∧ ∀ i,
        (injectiveSectionHomologyPresheaf (X := TopCat.of (PrimeSpectrum A)) F n).map
          (homOfLE (hf i)).op z = 0 :=
  affineSectionHomology_finiteBasicOpenVanishing _
    ((moduleSheafInjectiveResolution (X := TopCat.of (PrimeSpectrum A)) F).cocomplex_exactAt_succ n)
    U hU z

end SerrePositivity.KST.DerivedGeometry
