module
public import SerrePositivity.DifferentialGraded.Complexes.DiskContractible
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Module.Acyclic
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # 自由dg加群のsphere/diskとセル境界

freeSphere x nからの射はM(x)の次数nのcycle。
freeDisk x nからの射はM(x)の次数nの任意の要素。
全作用は既存の自由dg加群を再利用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev freeSphere (x : D) (n : ℤ) : ModuleCategory A D :=
  (freeAt x).obj (complexSphere A n)

abbrev freeDisk (x : D) (n : ℤ) : ModuleCategory A D :=
  (freeAt x).obj (complexDisk A n)

/-- 生成cellの境界包含。 -/
def freeCellBoundary (x : D) (n : ℤ) : freeSphere A D x (n + 1) ⟶ freeDisk A D x n :=
  (freeAt x).map (complexSphereToDisk A n)

/-- 自由sphereは評価複体のcycleを表現する。 -/
def freeSphereHomEquiv (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeSphere A D x n ⟶ M) ≃ complexCycles A ((moduleEvaluation A D x).obj M) n :=
  (freeHomEquiv A D x (complexSphere A n) M).trans
    (complexSphereHomEquiv A ((moduleEvaluation A D x).obj M) n)

/-- 自由diskは評価複体の任意の斉次生成元を表現する。 -/
def freeDiskHomEquiv (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeDisk A D x n ⟶ M) ≃ ((moduleEvaluation A D x).obj M).X n :=
  (freeHomEquiv A D x (complexDisk A n) M).trans
    (complexDiskHomEquiv A ((moduleEvaluation A D x).obj M) n)

/-- 自由diskの生成元指定は値域に自然。 -/
lemma freeDiskHomEquiv_naturality (x : D) (n : ℤ) {M N : ModuleCategory A D}
    (f : freeDisk A D x n ⟶ M) (g : M ⟶ N) :
    freeDiskHomEquiv A D x n N (f ≫ g) =
      ((moduleEvaluation A D x).map g).f n (freeDiskHomEquiv A D x n M f) := by
  simp only [freeDiskHomEquiv, Equiv.trans_apply, freeHomEquiv_naturality_right]
  exact complexDiskHomEquiv_naturality A n _ _

/-- 自由cellの境界に制限すると、生成元の微分となる。 -/
lemma freeCellBoundary_comp (x : D) (n : ℤ) (M : ModuleCategory A D)
    (f : freeDisk A D x n ⟶ M) :
    (freeSphereHomEquiv A D x (n + 1) M (freeCellBoundary A D x n ≫ f)).val =
      ((moduleEvaluation A D x).obj M).d n (n + 1) (freeDiskHomEquiv A D x n M f) := by
  simp only [freeSphereHomEquiv, freeDiskHomEquiv, freeCellBoundary, Equiv.trans_apply,
    freeHomEquiv_naturality_left]
  exact complexSphereToDisk_comp A n _

/-- 自由diskは任意dg圏でobjectwise acyclic。Hom_Dのflatnessは不要。 -/
lemma freeDisk_acyclic (x : D) (n : ℤ) : moduleAcyclic A D (freeDisk A D x n) := by
  intro y
  exact complexDiskTensor_acyclic A n _

/-- 生成するtrivial cellの入口：零加群から自由diskへの射は準同型。 -/
lemma freeDisk_zeroTo_quasiIso (x : D) (n : ℤ) :
    moduleQuasiIso A D (moduleZeroTo A D (freeDisk A D x n)) := by
  intro y
  rw [quasiIso_iff]
  intro i
  apply (quasiIsoAt_iff_exactAt _ i ?_).2
  · exact freeDisk_acyclic A D x n y i
  · have hz := (moduleEvaluation A D y).map_isZero (moduleZero_isZero A D)
    exact ExactAt.of_isZero ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).map_isZero hz)

end SerrePositivity.DifferentialGraded
