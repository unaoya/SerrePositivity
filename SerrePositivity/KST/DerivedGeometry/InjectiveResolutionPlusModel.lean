module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
概要：通常の injective 分解の整数添字拡張を bounded below の injective 模型にする。
方針：既存の分解の各項の injectivity を使い、同じ微分を injective 対象の充満部分圏へ持ち上げる。
規約：分解の存在・比較の存在を入力の未証明フィールドにしない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の単一対象上の導来切断の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] {X : C} (I : InjectiveResolution X)

/-- 概要：単一対象の複体を bounded below 複体へ持ち上げる。
方針：元の単一複体にその次数の下限を添える。
規約：整数次数。使われ方：TT §3、Toën §3.2 の分解の増大。 -/
def singleComplexPlus (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  (CochainComplex.plus C).lift (CochainComplex.singleFunctor C n)
    (fun _ => ⟨n, inferInstance⟩)

/--
概要：分解の整数添字への拡張を injective 対象の圏の複体へ持ち上げる。
方針：各項の既証の injectivity を添え、元の微分を同じ射として保持する。
規約：負次数は元の零拡張の零対象。
使われ方：TT §3、Toën §3.2 の右導来関手の injective 模型での計算。
-/
def injectiveResolutionLift : CochainComplex (InjectiveObject C) ℤ where
  X n := ⟨I.cochainComplex.X n, inferInstance⟩
  d i j := ObjectProperty.homMk (I.cochainComplex.d i j)
  shape i j h := by apply ObjectProperty.hom_ext; exact I.cochainComplex.shape i j h
  d_comp_d' i j k _ _ := by
    apply ObjectProperty.hom_ext
    exact I.cochainComplex.d_comp_d i j k

/--
概要：injective 対象の圏へ持ち上げた分解は零未満の次数で零。
方針：忠実な包含後の元の分解の零拡張と同じ複体であることを使う。
規約：下限は実際の零拡張から証明する。
使われ方：TT §3、Toën §3.2 の bounded below injective 模型。
-/
instance injectiveResolutionLift_isStrictlyGE : (injectiveResolutionLift I).IsStrictlyGE 0 := by
  apply (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
    (injectiveResolutionLift I) (InjectiveObject.ι C) 0).mp
  change I.cochainComplex.IsStrictlyGE 0
  infer_instance

/--
概要：通常の injective 分解の実際の bounded below injective 模型。
方針：同じ整数添字の複体へ零の下限を添える。
規約：分解の同型類だけでなく対象を構成する。
使われ方：TT §3・§8、Toën §3.2 の単一対象の右導来切断。
-/
def injectiveResolutionLiftPlus : CochainComplex.Plus (InjectiveObject C) :=
  ⟨injectiveResolutionLift I, ⟨0, inferInstance⟩⟩

/--
概要：通常の injective 分解の整数添字拡張を bounded below 複体として取る。
方針：元の分解の零拡張に既証の零の下限を添える。
規約：元の分解と同じ複体。
使われ方：TT §3、Toën §3.2 の右導来比較。
-/
def injectiveResolutionPlus : CochainComplex.Plus C :=
  ⟨I.cochainComplex, ⟨0, inferInstance⟩⟩

/--
概要：単一対象から bounded below injective 分解への元の準同型。
方針：分解の既存の増大鎖写像を充満部分圏の射へ束ねる。
規約：分解の元の射を保持する。
使われ方：TT §3、Toën §3.2 の単一対象の導来像の計算。
-/
def injectiveResolutionPlusι :
    (singleComplexPlus (C := C) 0).obj X ⟶ injectiveResolutionPlus I :=
  ObjectProperty.homMk I.ι'

variable [HasDerivedCategory C]

/--
概要：bounded below 分解の増大写像は元の導来局所化で同型。
方針：実際の injective 分解の準同型性を局所化の反転へ適用する。
規約：導来比較の存在を新たな仮定にしない。
使われ方：TT §3、Toën §3.2 の分解による右導来像の計算。
-/
instance injectiveResolutionPlusι_Q_isIso :
    IsIso (DerivedCategory.Plus.Q.map (injectiveResolutionPlusι I)) := by
  apply Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
  exact (show QuasiIso I.ι' from inferInstance)

end SerrePositivity.KST.DerivedGeometry
