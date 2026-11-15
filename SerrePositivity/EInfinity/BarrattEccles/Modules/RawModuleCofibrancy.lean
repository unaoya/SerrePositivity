module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleModel
public import SerrePositivity.EInfinity.Modules.SemifreeGradedProjectivity
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-!
# 同じ半自由加群の実 projective cofibrancy

概要：N01 の構成したモデルと元の半自由対象を照合する。
方針：全次数 Hom の全射性と擬同型性から閉零射を厳密に持ち上げる。
規約：モデル構造は構成済みのものを使い、対象を別の置換へ変えない。
使われ方：Keller, On differential graded categories, Theorem 3.2 (1) の cofibrant 対象。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

/-- 概要：元の半自由加群からの閉零射を全射擬同型へ厳密に持ち上げる。
方針：同じ全次数 Hom の全射性・擬同型性に境界持ち上げ判定を適用する。
規約：Keller Theorem 3.2 (1)、ホモトピーまでの等式には弱めない。
使われ方：同じ半自由対象の cofibrancy。 -/
lemma strictRawModuleSemifree_strict_lift (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hs : (projectiveFibrations A) ((strictRawModuleUnderlying X).map p))
    (hq : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) p) (g : P ⟶ N) :
    ∃ l : P ⟶ M, l ≫ p = g := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  have hs' : moduleDegreewiseSurjective A D p := by
    intro x
    have hx : x = Opposite.op DGAlgebraPoint.star := Subsingleton.elim _ _
    subst x
    exact hs
  obtain ⟨F⟩ := hP
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) M)
  let L := moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)
  let r : K ⟶ L := eHomWhiskerLeft (Complex A) P p
  have hr : QuasiIso r := moduleSemifree_postcompose_quasiIso A D ⟨F⟩ p hq
  have hrs (n : ℤ) : Function.Surjective (r.f n) :=
    moduleSemifreeFiltration_postcompose_surjective A D F p hs' n
  let z := cycleFromUnit L (ForgetEnrichment.homTo (Complex A) g)
  have hz : r.f 1 0 = L.d 0 1 z.val := by rw [map_zero, z.property]
  obtain ⟨a, ha, hra⟩ := complex_boundary_lifting_of_surjective_quasiIso A r hrs hr 0
    (0 : complexCycles A K 1) z.val hz
  let l : P ⟶ M := moduleMorphismOfCycle A D a ha
  refine ⟨l, ?_⟩
  apply (closedHomEquiv A (RightModule A D) P N).injective
  apply Subtype.ext
  change (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (l ≫ p))).val = z.val
  have he : (cycleFromUnit K (ForgetEnrichment.homTo (Complex A) l)).val = a :=
    moduleMorphismOfCycle_cycle A D a ha
  calc
    _ = r.f 0 (cycleFromUnit K (ForgetEnrichment.homTo (Complex A) l)).val :=
      (moduleHomCycle_postcompose A D l p).symm
    _ = r.f 0 a := congrArg (r.f 0) he
    _ = z.val := hra

/-- 概要：元の半自由対象は同じ実 projective モデルで cofibrant。
方針：元の自由 I の右類の照合と厳密持ち上げを使う。
規約：Keller Theorem 3.2 (1)、別の解像度を選ばない。
使われ方：M10 の bifibrant fiber 比較の入力。 -/
lemma strictRawModuleModelCategory_semifreeCofibrant (X : (operad A).Algebra)
    (P : SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X))) :
    let := strictRawModuleModelCategory A X
    IsCofibrant (ForgetEnrichment.of (Complex A) P.val) := by
  let := strictRawModuleModelCategory A X
  let Q : strictRawModuleCategory A X := ForgetEnrichment.of (Complex A) P.val
  apply (isCofibrant_iff_of_isInitial (initial.to Q) initialIsInitial).mpr
  apply (cofibration_iff _).mpr
  change (strictRawModuleGeneratingCofibrations A X).rlp.llp (initial.to Q)
  intro M N p hp
  rw [strictRawModuleGeneratingCofibrations_rlp A X] at hp
  constructor
  intro a b sq
  obtain ⟨l, hl⟩ := strictRawModuleSemifree_strict_lift A X P.property p hp.1
    ((strictRawModuleQuasiIso_eq A X).symm ▸ hp.2) b
  exact CommSq.HasLift.mk' { l := l, fac_left := initialIsInitial.hom_ext _ _, fac_right := hl }

end SerrePositivity.EInfinity.BarrattEccles
