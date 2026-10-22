module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionBaseChangeMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovKernelHomologyNaturality

/-!
概要：底変更した実 kernel のホモロジー射を、元の代数射の H⁻⁽ⁿ⁺¹⁾ 射へ同定する。
方針：元の kernel 同型の厳密な自然性と、元の層から得たホモロジー同型を合成する。
規約：選んだ同型と元の射を保持。使われ方：二切断射の π₂ の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B P Q : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyLE 0] (f : A ⟶ B) (n : ℤ)
  (b : P ⟶ postnikov R A n) (d : Q ⟶ postnikov R B n) (v : P ⟶ Q)
  (hs : b ≫ postnikovMap R f n = v ≫ d)

lemma postnikovBaseChangedKernelHomologyIso_naturality :
    homologyMap (postnikovBaseChangedKernelMap R f n b d v hs) (-(n + 1)) ≫
      (postnikovBaseChangedKernelHomologyIso R B n d).hom =
        (postnikovBaseChangedKernelHomologyIso R A n b).hom ≫ homologyMap f.hom (-(n + 1)) := by
  have he := congrArg (fun t => homologyMap t (-(n + 1)))
    (postnikovBaseChangedKernelIso_naturality R f n b d v hs)
  simp only [homologyMap_comp] at he
  change homologyMap (postnikovBaseChangedKernelMap R f n b d v hs) (-(n + 1)) ≫
      (homologyMap (postnikovBaseChangedKernelIso R B n d).hom (-(n + 1)) ≫
        (postnikovKernelHomologyIso R B n).hom) =
    (homologyMap (postnikovBaseChangedKernelIso R A n b).hom (-(n + 1)) ≫
      (postnikovKernelHomologyIso R A n).hom) ≫ homologyMap f.hom (-(n + 1))
  rw [← Category.assoc, he, Category.assoc, postnikovKernelHomologyIso_naturality,
    ← Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
