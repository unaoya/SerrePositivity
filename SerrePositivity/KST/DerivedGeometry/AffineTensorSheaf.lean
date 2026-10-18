module

public import SerrePositivity.KST.DerivedGeometry.AffineTensorComparison
public import SerrePositivity.KST.DerivedGeometry.BasisLocalComparison
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# アフィンの加群テンソル前層の層化と tilde の同型

概要：M ⊗_R O(U) の前層を R 加群の圏で層化すると tilde M が得られる。
方針：基本開上で比較射が同型であることから局所全単射性を示す。
規約：一般の開の切断と層化前のテンソル積を同一視しない。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン比較。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/--
概要：アフィンのテンソル前層から tilde への比較は局所単射。
方針：基本開上の線形同型と開基底の局所単射判定を使う。
規約：任意の R 加群に対する主張。
使われ方：KST D4、Toën §3.2 のアフィン層化比較。
-/
instance affineTensorToTilde_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R))
      (affineTensorToTilde M) :=
  locallyInjective_of_basis PrimeSpectrum.basicOpen PrimeSpectrum.isBasis_basic_opens
    (affineTensorToTilde M) (fun f => by
      change Function.Injective (affineTensorSectionMap M (PrimeSpectrum.basicOpen f))
      rw [affineTensorSectionMap_basic]
      exact (affineBasicTensorSectionsEquiv M f).injective)

/--
概要：アフィンのテンソル前層から tilde への比較は局所全射。
方針：基本開上の線形同型と開基底の局所全射判定を使う。
規約：一般の開の切断上での全射性は主張しない。
使われ方：KST D4、Toën §3.2 のアフィン層化比較。
-/
instance affineTensorToTilde_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R))
      (affineTensorToTilde M) :=
  locallySurjective_of_basis PrimeSpectrum.basicOpen PrimeSpectrum.isBasis_basic_opens
    (affineTensorToTilde M) (fun f => by
      change Function.Surjective (affineTensorSectionMap M (PrimeSpectrum.basicOpen f))
      rw [affineTensorSectionMap_basic]
      exact (affineBasicTensorSectionsEquiv M f).surjective)

/--
概要：前層比較を R 加群層として層化すると同型になる。
方針：局所全単射な射が層化で同型になることを使う。
規約：層化の値域を R 加群の圏とする。
使われ方：KST D4、Toën §3.2 のアフィンの係数環層との比較の入力。
-/
instance affineTensorToTilde_sheafify_isIso :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)).map
      (affineTensorToTilde M)) :=
  ((Opens.grothendieckTopology (Spec R)).W_iff _).mp
    ((Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective (affineTensorToTilde M))

/--
概要：アフィンのテンソル前層の層化は tilde M の基礎 R 加群層と標準同型。
方針：層化した比較射と、層である値域に対する層化の余単位を合成する。
規約：選んだ基本開ごとの同型を独立に貼り合わせるのではなく自然な比較から構成する。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン模型。
-/
def affineTensorSheafIso :
    (presheafToSheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)).obj
      (affineModuleTensorPresheaf M) ≅ modulesSpecToSheaf.obj (tilde M) :=
  (asIso ((presheafToSheaf (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)).map
    (affineTensorToTilde M))).trans
      (asIso ((sheafificationAdjunction (Opens.grothendieckTopology (Spec R))
        (ModuleCat.{u} R)).counit.app (modulesSpecToSheaf.obj (tilde M))))

/--
概要：層化の単位の後に標準同型を合成すると、元の切断の比較になる。
方針：層化の単位の自然性と、単位・余単位の三角恒等式を使う。
規約：アフィン比較の指定された射への両立を明示する。
使われ方：KST D4、Toën §3.2 の環層の作用と加群層の比較。
-/
lemma toSheafify_affineTensorSheafIso :
    toSheafify (Opens.grothendieckTopology (Spec R)) (affineModuleTensorPresheaf M) ≫
      (affineTensorSheafIso M).hom.hom = affineTensorToTilde M := by
  change toSheafify _ _ ≫ sheafifyMap _ (affineTensorToTilde M) ≫
    ((sheafificationAdjunction _ _).counit.app (modulesSpecToSheaf.obj (tilde M))).hom = _
  rw [← toSheafify_naturality_assoc]
  simp

end SerrePositivity.KST.DerivedGeometry
