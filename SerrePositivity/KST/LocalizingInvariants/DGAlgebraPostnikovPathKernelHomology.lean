module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeKernelHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedLayer

/-!
概要：元の底経路による隣接 Postnikov 拡大の kernel 比較は、元の係数同型を保つ。
方針：底の切断の下端消滅から kernel 包含の単射性を導き、共通模型の比較を使う。
規約：指定ホモロジー同型を保持。使われ方：同じ底上の π₂ 逆の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [P.X.IsStrictlyLE 0] (n : ℤ)
  (a b : P ⟶ postnikov R B n) (w : Path.Witness R a b)

local instance pathKernelUpper_nonpositive : (postnikov R B (n + 1)).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R B (n + 1)

lemma postnikovPathKernelHomologyIso_original :
    (PathBaseChange.kernelHomologyIso R a b
      (postnikovTransition R B (n + 1) n (by omega)) w (-(n + 1))).hom ≫
      (postnikovBaseChangedKernelHomologyIso R B n b).hom =
        (postnikovBaseChangedKernelHomologyIso R B n a).hom := by
  let q := postnikovTransition R B (n + 1) n (by omega)
  have hq : Epi q.hom := postnikovTransition_epi R B (n + 1) n (by omega)
  have hk : QuasiIsoAt (kernel.ι q.hom) (-(n + 1)) :=
    cochainKernelInclusion_quasiIsoAt q.hom (-(n + 1))
      ((postnikov R B n).X.isZero_of_isGE (-n) (-(n + 1)) (by omega))
      ((postnikov R B n).X.isZero_of_isGE (-n) (-(n + 1) - 1) (by omega))
  have ht := PathBaseChange.kernelHomologyIso_original R a b q w (-(n + 1))
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫ (postnikovKernelHomologyIso R B n).hom) ht)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
