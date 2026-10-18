module

public import SerrePositivity.KST.DerivedGeometry.OpenCechLowDegree
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：実際の Čech 複体の増大の零次数完全性。
方針：低次数の比較と層条件の核を短複体同型で結ぶ。
規約：Čech の符号は右制限から左制限を引く向きに固定する。
使われ方：TT §3・§8、Toën §3.2 の Čech 分解への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w a b
open CategoryTheory Limits Preadditive TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{w} A]
  {X : TopCat.{w}} (F : TopCat.Sheaf A X) {ι : Type w} (U : ι → Opens X)
open TopCat.Presheaf.SheafConditionEqualizerProducts

/--
概要：切断から実際の Čech 第0項への増大。
方針：被覆上の制限と第0項の比較の逆を合成する。
規約：被覆の和集合上の切断から出発する。
使われ方：TT §3、Toën §3.2 の Čech 増大。
-/
def sheafCechAugmentationZero : F.obj.obj (.op (⨆ i, U i)) ⟶
    ((cechComplexFunctor U).obj F.obj).X 0 :=
  res F.obj U ≫ (openCechZeroIso U F.obj).inv

/--
概要：Čech 増大と最初の微分の合成は零。
方針：第1項の比較で単射性を使い、制限の可換性へ帰着する。
規約：元の Čech 微分そのものを扱う。
使われ方：TT §3、Toën §3.2 の増大短複体。
-/
lemma sheafCechAugmentationZero_comp_d :
    sheafCechAugmentationZero F U ≫ ((cechComplexFunctor U).obj F.obj).d 0 1 = 0 := by
  apply (cancel_mono (openCechOneIso U F.obj).hom).mp
  dsimp only [sheafCechAugmentationZero]
  simp only [Category.assoc, openCech_firstDifferential, comp_sub, zero_comp]
  exact sub_eq_zero.mpr (w F.obj U).symm

/--
概要：Čech 増大と最初の微分の短複体。
方針：構成済みの増大と合成零の証明を束ねる。
規約：中央と右端は実際の Čech 複体の第0・第1項。
使われ方：TT §3・§8、Toën §3.2 の零次数。
-/
def sheafCechAugmentationShortComplex : ShortComplex A :=
  ShortComplex.mk (sheafCechAugmentationZero F U) _ (sheafCechAugmentationZero_comp_d F U)

/--
概要：Čech 増大短複体と層条件の短複体の同型。
方針：第0・第1項の比較を使い、第1項側で符号を反転する。
規約：符号反転は比較同型に含め、微分は変更しない。
使われ方：TT §3・§8、Toën §3.2 の貼り合わせの移送。
-/
def sheafCechAugmentationShortComplexIso :
    sheafCechAugmentationShortComplex F U ≅ sheafCoverShortComplex F U :=
  ShortComplex.isoMk (Iso.refl _) (openCechZeroIso U F.obj) (-(openCechOneIso U F.obj))
    (by simp [sheafCechAugmentationShortComplex, sheafCechAugmentationZero,
      sheafCoverShortComplex])
    (by
      have h := congrArg (fun k => (openCechZeroIso U F.obj).hom ≫ k)
        (openCech_firstDifferential U F.obj)
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
      simpa [sheafCechAugmentationShortComplex, sheafCoverShortComplex, comp_sub, comp_neg]
        using (congrArg Neg.neg h).symm)

/--
概要：実際の Čech 増大は零次数で完全。
方針：短複体同型で層条件から得た完全性を移す。
規約：被覆の有限性と準連接性は不要。
使われ方：TT §3・§8、Toën §3.2 の Čech 分解。
-/
lemma sheafCechAugmentation_exact : (sheafCechAugmentationShortComplex F U).Exact :=
  (ShortComplex.exact_iff_of_iso (sheafCechAugmentationShortComplexIso F U)).mpr
    (sheafCoverShortComplex_exact F U)

/--
概要：実際の Čech 増大は mono。
方針：層条件の制限の単射性と比較同型を使う。
規約：被覆の和集合上の切断を用いる。
使われ方：TT §3・§8、Toën §3.2 の増大の一意性。
-/
instance sheafCechAugmentation_mono : Mono (sheafCechAugmentationZero F U) := by
  change Mono ((sheafCoverShortComplex F U).f ≫ (openCechZeroIso U F.obj).inv)
  infer_instance

/--
概要：Čech 増大から零次数のサイクルへの実際の持ち上げ。
方針：増大と微分の合成が零であることを使う。
規約：Mathlib のサイクルの核を用いる。
使われ方：TT §3、Toën §3.2 の Čech の H⁰ 比較。
-/
def sheafCechCyclesLift : F.obj.obj (.op (⨆ i, U i)) ⟶
    ((cechComplexFunctor U).obj F.obj).cycles 0 :=
  ((cechComplexFunctor U).obj F.obj).liftCycles (sheafCechAugmentationZero F U) 1
    (by simp) (sheafCechAugmentationZero_comp_d F U)

/--
概要：層の増大は Čech の零次数のサイクルと同型。
方針：完全性と mono から核への持ち上げの同型性を得る。
規約：同型性を仮定として追加しない。
使われ方：TT §3、Toën §3.2 の Čech の H⁰ 比較。
-/
instance sheafCechCyclesLift_isIso : IsIso (sheafCechCyclesLift F U) :=
  (CochainComplex.isIso_liftCycles_iff _ _ (sheafCechAugmentationZero_comp_d F U)).mpr
    ⟨sheafCechAugmentation_exact F U, inferInstance⟩

/--
概要：実際の Čech 複体の H⁰ は被覆の和集合上の切断と同型。
方針：負次数からの微分がないことと増大からサイクルへの同型を合成する。
規約：任意の層・任意の被覆に対する実際のコホモロジー。
使われ方：TT §3・§8、Toën §3.2 の Čech 分解。
-/
def sheafCechH0Iso : ((cechComplexFunctor U).obj F.obj).homology 0 ≅
    F.obj.obj (.op (⨆ i, U i)) :=
  ((cechComplexFunctor U).obj F.obj).isoHomologyπ₀.symm ≪≫
    (asIso (sheafCechCyclesLift F U)).symm

/--
概要：被覆の和集合上の切断を集中させた複体から Čech 複体への増大。
方針：零次数の増大と合成零から標準の単一項複体の射を構成する。
規約：元の Čech 複体の全次数を保持する。
使われ方：TT §3・§8、Toën §3.2 のアフィン Čech 分解。
-/
def sheafCechAugmentation :
    (CochainComplex.single₀ A).obj (F.obj.obj (.op (⨆ i, U i))) ⟶
      (cechComplexFunctor U).obj F.obj :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨sheafCechAugmentationZero F U, sheafCechAugmentationZero_comp_d F U⟩

/--
概要：層の Čech 増大は零次数のコホモロジー同型を誘導する。
方針：単一項複体からの射の局所準同型判定に完全性と mono を渡す。
規約：準同型性を正次数ではまだ主張しない。
使われ方：TT §3・§8、Toën §3.2 のアフィン Čech 分解。
-/
instance sheafCechAugmentation_quasiIsoAt_zero : QuasiIsoAt (sheafCechAugmentation F U) 0 := by
  have hn : (ComplexShape.up ℕ).next 0 = 1 := (ComplexShape.up ℕ).next_eq' rfl
  rw [quasiIsoAt_iff' _ 0 0 1 (by simp) hn]
  apply (ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)).mpr
  simpa [sheafCechAugmentation, sheafCechAugmentationShortComplex,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor', hn] using
    (show (sheafCechAugmentationShortComplex F U).Exact ∧
      Mono (sheafCechAugmentationZero F U) from
        ⟨sheafCechAugmentation_exact F U, inferInstance⟩)

end SerrePositivity.KST.DerivedGeometry
