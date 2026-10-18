module

public import SerrePositivity.KST.DerivedGeometry.FreeFormalSheafHomIso
public import SerrePositivity.KST.DerivedGeometry.FreeSheafCechAugmentation
public import SerrePositivity.KST.DerivedGeometry.AlternatingHomComparison
public import SerrePositivity.KST.DerivedGeometry.InjectiveHomExact
public import SerrePositivity.KST.DerivedGeometry.CechFunctorComparison
public import SerrePositivity.KST.DerivedGeometry.SheafCechAugmentation

/-!
概要：injective 加群層の通常の Čech 余鎖複体の正次数完全性。
方針：自由層の Čech 鎖複体の完全性に Hom を適用し、実際の切断の Čech と比較する。
規約：通常の Mathlib の Čech 複体を使い、非輪状性を仮定として追加しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech と右導来切断の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)

/--
概要：自由層の形式的余積による Čech の交代面鎖複体。
方針：形式的 Čech を自由層の関手で評価し交代面複体を取る。
規約：層化して構成した複体との同型を次に証明する。
使われ方：TT §3・§8、Toën §3.2 の Čech の Hom 比較。
-/
def freeFormalSheafCechComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((FormalCoproduct.mk ι U).cech ⋙ freeFormalSheafFunctor R X)

/--
概要：層化した自由 Čech 複体と自由層で評価した Čech 複体は同型。
方針：加法的な層化関手と交代面鎖複体の比較を使う。
規約：増大先は左側の鎖複体の定義だけに現れる。
使われ方：TT §3、Toën §3.2 の自由 Čech の Hom 比較。
-/
def freeSheafCechFormalIso (V : Opens X) (hU : ∀ i, U i ≤ V) :
    freeSheafCechComplex R X U V hU ≅ freeFormalSheafCechComplex R X U :=
  (alternatingFaceCompMapIso (presheafToSheaf _ _)).app
    (freePresheafCechAugmented R X U V hU).left

/--
概要：自由層で評価した Čech 鎖複体は被覆について全正次数で完全。
方針：層化した Čech の完全性を同じ複体の比較同型で移す。
規約：任意の被覆を扱う。
使われ方：TT §3・§8、Toën §3.2 の Hom の完全性への入力。
-/
lemma freeFormalSheafCech_exactAt (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    (freeFormalSheafCechComplex R X U).ExactAt (n + 1) :=
  (exactAt_iff_of_quasiIsoAt
    (freeSheafCechFormalIso R X U ⊤ (fun _ => le_top)).hom (n + 1)).mp
      (freeSheafCech_exactAt R X U ⊤ (fun _ => le_top) hcover n)

variable (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/--
概要：自由 Čech 鎖複体への反変 Hom の余鎖複体。
方針：鎖複体の対に加法的 Yoneda 関手を適用する。
規約：加法群値で全次数と微分を保持する。
使われ方：TT §3・§8、Toën §3.2 の injective Čech 計算。
-/
def freeSheafCechHomComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((preadditiveYoneda.obj I).mapHomologicalComplex (.up ℕ)).obj
    (freeFormalSheafCechComplex R X U).op

/--
概要：自由 Čech への Hom の余鎖複体は通常の切断の Čech と同型。
方針：交代面の反変比較と自由層の Hom と切断の自然同型を合成する。
規約：元の Mathlib の Čech 微分と一致する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech 比較。
-/
def freeSheafCechHomIso : freeSheafCechHomComplex R X U I ≅
    (cechComplexFunctor U).obj (I.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  alternatingFaceContravariantIso (preadditiveYoneda.obj I)
      ((FormalCoproduct.mk ι U).cech ⋙ freeFormalSheafFunctor R X) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.isoWhiskerLeft (FormalCoproduct.mk ι U).cech.rightOp
        (freeFormalSheafHomNatIso R X I))

/--
概要：injective 層への自由 Čech の Hom は全正次数で完全。
方針：自由 Čech 鎖複体の完全性に反変 Hom の完全性を適用する。
規約：injective の存在を入力にせず、任意の injective 対象について述べる。
使われ方：TT §3・§8、Toën §3.2 の Čech の非輪状性。
-/
lemma freeSheafCechHom_exactAt [Injective I] (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    (freeSheafCechHomComplex R X U I).ExactAt (n + 1) :=
  injectiveHom_map_exact I ((freeFormalSheafCechComplex R X U).op.sc (n + 1))
    (freeFormalSheafCech_exactAt R X U hcover n).op

/--
概要：injective 加群層の基礎加法群の通常の Čech 複体は全正次数で完全。
方針：証明済みの Hom 余鎖複体の完全性を実際の Čech へ比較同型で移す。
規約：任意の開被覆を扱い、被覆の有限性や係数の平坦性は不要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech と層コホモロジーの比較。
-/
lemma injectiveCechAb_exactAt [Injective I] (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj
      (I.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (n + 1) :=
  (exactAt_iff_of_quasiIsoAt (freeSheafCechHomIso R X U I).hom (n + 1)).mp
    (freeSheafCechHom_exactAt R X U I hcover n)

/--
概要：injective 加群層の加群値の有限 Čech 複体は全正次数で完全。
方針：加法群への忘却と有限 Čech の比較を介して完全性を反映する。
規約：忘却後だけでなく元の R 加群値の複体について述べる。
使われ方：TT §3・§8、Toën §3.2 の右導来切断との Čech 比較。
-/
lemma injectiveCech_exactAt [Injective I] [Finite ι] (hcover : (⨆ i, U i) = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj I.obj).ExactAt (n + 1) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let e := finiteCechFunctorIso F U I.obj
  have h := (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
    (injectiveCechAb_exactAt R X U I hcover n)
  exact (((cechComplexFunctor U).obj I.obj).sc (n + 1)).exact_map_iff_of_faithful F |>.mp h

/--
概要：injective 加群層の有限被覆の Čech 増大は準同型。
方針：零次数の層条件と injective の正次数の Čech 完全性を合わせる。
規約：各項は元の層の R 加群としての実際の切断。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech と層コホモロジーの比較。
-/
lemma injectiveCechAugmentation_quasiIso [Injective I] [Finite ι]
    (hcover : (⨆ i, U i) = ⊤) : QuasiIso (sheafCechAugmentation I U) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => infer_instance
  | succ n =>
    apply (quasiIsoAt_iff_exactAt _ (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ n)).mpr
    exact injectiveCech_exactAt R X U I hcover n

end SerrePositivity.KST.DerivedGeometry
