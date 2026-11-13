module
public import SerrePositivity.KST.SConstruction.McCarthyRhoRaw
public import SerrePositivity.KST.SConstruction.McCarthySpanGapped
public import SerrePositivity.KST.SConstruction.PointwiseCofiberPushout
public import SerrePositivity.KST.SConstruction.PointwiseGappedPushout
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful

/-! # McCarthy の ρ の cofiber 値への持ち上げ
概要：元の C 内で選んだ raw ρ の全頂点が cofiber であることを証明する。
方針：cofiber 図式内の押し出しと同じ span 上で比較する。
規約：raw の選択・自然性・端点を保持する。使われ方：加法性の実ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の ρ の正方形は全区間で cofiber。
方針：cofiber 図式の span の点ごとの押し出し閉性。
規約：gapped 性や fiber 条件は仮定しない。使われ方：元の ρ の持ち上げ。 -/
lemma mcCarthyRhoRaw_isCofiber {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) (a : (arNerve n) _⦋0⦌) :
    IsCofiberDiagramVertex ((mcCarthyRhoRaw z A α τ E h).app (Opposite.op ⦋0⦌) a) :=
  pointwiseCofiberPushout_vertex (mcCarthySpan z A α τ E h) a

/-- 概要：元の ρ をそのまま cofiber 図式の族へ持ち上げる。
方針：点ごとの押し出しの持ち上げを適用する。
規約：C 内の選択を変更しない。使われ方：McCarthy の実ホモトピーの候補。 -/
def mcCarthyRho {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : arNerve n ⟶ cofiberDiagrams C :=
  pointwiseCofiberPushout (mcCarthySpan z A α τ E h)

/-- 概要：cofiber 値への持ち上げの包含は元の raw ρ。
方針：全部分複体への持ち上げの等号。
規約：全単体での厳密な一致。使われ方：自然性・端点の回収。 -/
lemma mcCarthyRho_ι {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRho z A α τ E h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      mcCarthyRhoRaw z A α τ E h := rfl

/-- 概要：cofiber 値の ρ の零時刻は元の図式 E。
方針：包含の単射性で raw の正規化を反映する。
規約：cofiber 図式全体の厳密な等号。使われ方：ホモトピーの恒等端点。 -/
lemma mcCarthyRho_timeZero {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : mcCarthyRho z A α (OrderHom.const _ 0) E h = E := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).1
  rw [mcCarthyRho_ι, mcCarthyRhoRaw_timeZero]

/-- 概要：cofiber 値の ρ は全ての面・退化と可換。
方針：包含後の自然性を単射性で反映する。
規約：左 fiber 条件の証明の選択によらない。使われ方：単体ホモトピーへの束ね。 -/
lemma mcCarthyRho_pre {l n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) (σ : Fin (l + 1) →o Fin (n + 1))
    (h' : (arNerveMap σ ≫ E) ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = arNerveMap (α.comp σ) ≫ A) :
    mcCarthyRho z A (α.comp σ) (τ.comp σ) (arNerveMap σ ≫ E) h' =
      arNerveMap σ ≫ mcCarthyRho z A α τ E h := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).1
  rw [mcCarthyRho_ι, Category.assoc, mcCarthyRho_ι, mcCarthyRhoRaw_pre]

/-- 概要：A と元の E が gapped なら cofiber 値の ρ は gapped。
方針：span の三頂点の gapped 性と点ごとの押し出し閉性。
規約：出力の gapped 性は追加仮定にしない。使われ方：ρ の S_n への持ち上げ。 -/
lemma mcCarthyRho_isGapped {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (hA : IsGapped A)
    (α : Fin (n + 1) →o Fin (m + 1)) (τ : Fin (n + 1) →o Fin 2)
    (E : arNerve n ⟶ cofiberDiagrams C) (hE : IsGapped E)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : IsGapped (mcCarthyRho z A α τ E h) :=
  pointwiseCofiberPushout_isGapped (mcCarthySpan z A α τ E h)
    (mcCarthySpan_isGapped_vertex z A hA α τ E hE h)

/-- 概要：元の C 内の raw ρ も正方形を値とする gapped 図式。
方針：cofiber 値の gapped 性を完全な包含で移す。
規約：元の raw ρ の射そのものに対する結論。使われ方：次の各角の厳密な回収。 -/
lemma mcCarthyRhoRaw_isGapped {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (hA : IsGapped A)
    (α : Fin (n + 1) →o Fin (m + 1)) (τ : Fin (n + 1) →o Fin 2)
    (E : arNerve n ⟶ cofiberDiagrams C) (hE : IsGapped E)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : IsGapped (mcCarthyRhoRaw z A α τ E h) := by
  rw [← mcCarthyRho_ι]
  exact (mcCarthyRho_isGapped z A hA α τ E hE h).postcomp _
    (cofiberInclusion_preservesSConstructionData C)

end SerrePositivity.KST.SConstruction
