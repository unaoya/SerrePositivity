module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaCohomotopy
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneCohomotopy
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneCircle

/-!
# 指定計算段の π/H 比較の全複体射に対する自然性

DAG XIII §2.2 の整数 π/H の全関手比較への前段。同じシフトのホモロジー同型と
添字の同一視を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedGroupMap)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable {A : Type u} [CommRing A]

lemma homologyIndexIso_naturality {M N : Complex A} (f : M ⟶ N)
    {i j : ℤ} (h : i = j) :
    homologyMap f i ≫ (eqToIso (congrArg (fun k => N.homology k) h)).hom =
      (eqToIso (congrArg (fun k => M.homology k) h)).hom ≫ homologyMap f j := by
  subst j
  simp

lemma levelPiCohomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N) (r n : ℕ)
    (a : KanHomotopyGroup (((levelPointedFunctor A r).obj M).right) n
      ((levelPointedFunctor A r).obj M).basepoint) :
    levelPiCohomologyEquiv A N r n
      (pointedGroupMap n ((levelPointedFunctor A r).map f) a) =
      Multiplicative.ofAdd ((homologyMap f ((r : ℤ) - ((n : ℤ) + 1))).hom
        (Multiplicative.toAdd (levelPiCohomologyEquiv A M r n a))) := by
  let sh := (homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
    (r : ℤ) (-((n + 1 : ℕ) : ℤ)) ((r : ℤ) - ((n : ℤ) + 1)) (by omega)
  have hπ := gammaPiCohomologyEquiv_naturality A (f⟦(r : ℤ)⟧') n a
  have h₁ := congrArg (fun t => Multiplicative.ofAdd
    ((sh.app N).hom.hom (Multiplicative.toAdd t))) hπ
  have h₂ := congrArg (fun k => Multiplicative.ofAdd (k.hom
    (Multiplicative.toAdd (gammaPiCohomologyEquiv A (M⟦(r : ℤ)⟧) n a))))
    (sh.hom.naturality f)
  exact h₁.trans h₂

lemma levelPiCohomologyEquivAt_naturality {M N : Complex A} (f : M ⟶ N)
    (j : ℤ) (r n : ℕ) (hj : (n : ℤ) + 1 = j + (r : ℤ))
    (a : KanHomotopyGroup (((levelPointedFunctor A r).obj M).right) n
      ((levelPointedFunctor A r).obj M).basepoint) :
    levelPiCohomologyEquivAt A N j r n hj
      (pointedGroupMap n ((levelPointedFunctor A r).map f) a) =
      Multiplicative.ofAdd ((homologyMap f (-j)).hom
        (Multiplicative.toAdd (levelPiCohomologyEquivAt A M j r n hj a))) := by
  have he : (r : ℤ) - ((n : ℤ) + 1) = -j := by omega
  have h₁ := congrArg (fun t => Multiplicative.ofAdd
    ((eqToIso (congrArg (fun k => N.homology k) he)).hom.hom (Multiplicative.toAdd t)))
      (levelPiCohomologyEquiv_naturality f r n a)
  have h₂ := congrArg (fun k => Multiplicative.ofAdd (k.hom
    (Multiplicative.toAdd (levelPiCohomologyEquiv A M r n a))))
    (homologyIndexIso_naturality f he)
  exact h₁.trans h₂

end SerrePositivity.EInfinity.PowerOperation
