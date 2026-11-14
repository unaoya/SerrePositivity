-- 将来の置き場所：EInfinity の上（余単体的可換環の Tot の E∞ 構造。BS 固有ではない。調整役と相談）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-11、a2-design.md §2.2。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.Homology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
-- 本ファイルは drafts/Shared/CosimplicialCupProduct.lean と drafts/Sheaves/{CechConerveLimit,CAlgValued}.lean を使う。
-- 11-07（a1-design §10.5）：末尾の 3 節（厳密な自然変換の辺、余単体的 cdga の Tot、Tot と係数制限）は drafts/DerivedGeneral/ScalarRestriction.lean も使う。

/-!
# 余単体的可換環の Tot の E∞ 構造と、CAlg 値の脚注 10

## 概要
余単体的可換 A 代数 X^• の非正規化余鎖複体に Barratt–Eccles 作用素の作用を入れ（McClure–Smith、Berger–Fresse：余単体的可換環の
余鎖は E∞ 代数）、CAlg_A の対象 Tot_{E∞}(X^•) を得る。その下の複体は交代余面複体、H^* の環構造は Alexander–Whitney の cup 積
（Shared/CosimplicialCupProduct）に一致する。さらに、Tot_{E∞}(X^•) は CAlg_A における余単体的対象 [n] ↦ X^n の Δ 上の極限で、
弱終対象の Čech 脈体の補題（S3）の CAlg_A 版により、環の前層の CAlg 値 RΓ が Čech–Alexander 模型の Tot_{E∞} に E∞ 代数として一致する。

## 方針
E∞ 構造は EInfinity の Barratt–Eccles 作用素（`Operad`、`CochainComonoid` などの余鎖の余モノイド構造）で、余単体的可換環の
正規化余鎖に McClure–Smith の構成を当てる。極限との同一視は、U : CAlg_A → D(A) が極限錐を保ち反映すること（Sheaves/CAlgValued）と、
D(A) 側の G10（Δ 上の極限 ＝ 全複体）。

## 規約
E∞ 構造の明示的な構成は EInfinity の operad の形に合わせる（要確認：EInfinity の Barratt–Eccles 作用素が余鎖に作用する形で公開されているか）。
正規化と非正規化は擬同型（Dold–Kan）。ただし W9-I-24：複体の擬同型だけでは E∞ 構造の比較にならない。**正規化模型を選んで** CAlg の
ホモトピー整合的な錐を構成し（U で見た underlying cone が各項への射影の錐に一致すること）、AW 積との比較を示す。非正規化模型への
E∞ 構造の移送を使うなら、その比較射を明記する。

## 使われ方
A2-2（Δ_0 の CAlg 値が Čech–Alexander 模型の Tot_{E∞}）、A1 の D27（模型の cup 積と抽象的な環構造の一致）、A4（Frobenius 余極限の E∞ 構造）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.Cosimplicial

open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

-- CosimplicialAlgebra は同じ型の本体 HomologicalAlgebra.Cosimplicial.Algebra を使う。

/-- 概要：BS 著者版 Construction 7.6 の余単体的可換環の Tot。
方針：EInfinityTheory が供給する実現関手を用いる。
規約：指定錐と下の交代余面複体との比較も同じ界面から読む。
使われ方：A2 の Δ_0。 -/
def totEInfinityFunctor : nerve (CosimplicialAlgebra A) ⟶ E.CAlg A := E.ofCosimplicial A

abbrev totEInfinity (X : CosimplicialAlgebra A) :=
  (totEInfinityFunctor (E := E) A).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)

/-- 小さい Δ の nerve だけを持ち上げ、各項を離散 E∞ 代数に送る。 -/
def totDiagram (X : CosimplicialAlgebra A) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ E.CAlg A := cosimplicialNerve X ≫ E.discrete A

/-- 概要：Tot_{E∞} の下の複体は交代余面複体（`alternatingCofaceMapComplex`）。
方針：構成から。
規約：D(A) の同値。
使われ方：A0 の D(A) 値の Tot との一致。 -/
def totEInfinity_forget (X : CosimplicialAlgebra A) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A (i : ℤ) ((E.forget A).app _ (totEInfinity (E := E) A X)) ≅
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (X ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A)).homology i := by
  let K := (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj
    (X ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A)
  have hstrict := (E.strictToD_homologyIso A (i : ℤ)).app ((cosimplicialCochains A).obj X)
  simp only [Functor.comp_obj, ordinaryToHoNerve, hoMap, SSet.hoFunctor_map,
    Functor.toCatHom_toFunctor, SSet.mapHomotopyCategory_obj_mk, nerveEquiv, Equiv.symm] at hstrict
  change (cohomologyOnHo A (i : ℤ)).obj
    (HomotopyCategory.mk ((E.strictToD A).app _
      (ComposableArrows.mk₀ ((cosimplicialCochains A).obj X)))) ≅ _ at hstrict
  have hforget := (cohomologyOnHo A (i : ℤ)).mapIso
    ((E.ofCosimplicial_forget A).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
  simp only [SSet.comp_app, types_comp_apply, ConcreteCategory.comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex,
    nerveMap_app_mk₀] at hforget
  change _ ≅ (cohomologyOnHo A (i : ℤ)).obj
    (HomotopyCategory.mk ((E.strictToD A).app _
      ((nerveMap (cosimplicialCochains A)).app _ (ComposableArrows.mk₀ X)))) at hforget
  rw [nerveMap_app_mk₀] at hforget
  change (cohomologyOnHo A (i : ℤ)).obj
    (HomotopyCategory.mk ((E.forget A).app _ ((E.ofCosimplicial A).app _
      (ComposableArrows.mk₀ X)))) ≅ _ at hforget
  have hpoint (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
      (cohomologyOnHo A (i : ℤ)).obj (HomotopyCategory.mk x) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A (i : ℤ) x := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor A (i : ℤ)).obj _ =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor A (i : ℤ)).obj _
    congr 1 <;> rfl
  simpa only [totEInfinity, totEInfinityFunctor, hpoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex] using
    (hforget ≪≫ hstrict ≪≫
      K.extendHomologyIso ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl)

/-- A 線形な比較を、cup に使うコホモロジーの加法群に移す。 -/
def totEInfinity_forget_cohomology (X : CosimplicialAlgebra A) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A (i : ℤ) ((E.forget A).app _ (totEInfinity (E := E) A X)) ≃+
      cohomology (X ⋙ Under.forget _) i := by
  refine (totEInfinity_forget (E := E) A X i).toLinearEquiv.toAddEquiv.trans
    (AddEquiv.trans ?_ (cohomologyEquivHomology (X ⋙ Under.forget _) i).symm)
  sorry -- 加群から加法群への忘却は交代余面複体とホモロジーを保つ

/-- 交代余面複体は次数零から始まる。 -/
theorem totEInfinity_forget_negative (X : CosimplicialAlgebra A) (i : ℤ) (hi : i < 0) :
    Limits.IsZero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A i ((E.forget A).app _ (totEInfinity (E := E) A X))) := by
  sorry -- ofCosimplicial_forget と strictToD_homologyIso で零延長複体に移す

/-- 概要：Tot_{E∞} の H^* の環構造は cup 積（Shared/CosimplicialCupProduct）に一致。
方針：E∞ 構造の二項演算 μ_0 が Alexander–Whitney の cup 積（Barratt–Eccles の次数 0 の成分）。
規約：—
使われ方：A1 の D27。×：全次数の π_* の積を与える基盤名がなく、π₀ の環だけではこの比較を述べられない（M14）。 -/
theorem totEInfinity_cohomologyRing (X : CosimplicialAlgebra A) : True := by trivial

/-- 概要：Tot_{E∞}(X^•) は CAlg_A における余単体的図式 [n] ↦ X^n（離散 E∞ 代数）の Δ 上の極限。
方針：同じ Tot の頂点に対し、界面が供給する指定極限錐を用いる。
規約：錐は CAlg_A の JoinCone。
使われ方：CAlg 値の脚注 10。 -/
def totEInfinityCone (X : CosimplicialAlgebra A) :
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (totDiagram (E := E) A X) // c.vertex = totEInfinity (E := E) A X} := by
  let c := E.ofCosimplicial_cone A X
  exact ⟨c.val, c.property.1⟩

theorem totEInfinity_isLimitCone (X : CosimplicialAlgebra A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (totEInfinityCone (E := E) A X).val := (E.ofCosimplicial_cone A X).property.2

/-- 概要：余単体的 A 代数の射 X → Y は Tot_{E∞} の E∞ 代数の射を誘導し、関手的。
方針：構成の自然性。
規約：—
使われ方：Δ_0 の多項式代数の射についての関手性、Frobenius（半線形は別）。 -/
def totEInfinity_map {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    SSet.Edge (totEInfinity (E := E) A X) (totEInfinity (E := E) A Y) :=
  (nerve.edgeMk f).map (totEInfinityFunctor (E := E) A)

/-- 概要：交代余面複体の擬同型を誘導する余単体的 A 代数の射は、Tot_{E∞} の可逆な辺を与える（11-07、a1-design §10.5）。
方針：U : CAlg_A → D(A) は保存的（Sheaves/CAlgValued）、`totEInfinity_forget` は射について自然。
規約：仮定は `alternatingCofaceMapComplex` の `QuasiIso`（A1 の `extraCech_comparison`・`pdCechNerveMap_quasiIso` と同じ形）。
使われ方：A1-5 の各対象での可逆性（`wittBigBridge_isInvertible` など）。 -/
theorem totEInfinity_map_isInvertible {X Y : CosimplicialAlgebra A} (f : X ⟶ Y)
    (hf : QuasiIso ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      (Functor.whiskerRight f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (totEInfinity_map (E := E) A f).toTruncated := by
  sorry -- E.forget_conservative。E.strictToD_homologyIso と E.ofCosimplicial_forget の自然性で
        -- 全次数のホモロジーの射が同型。零延長で QuasiIso を保つ

/-- 概要：脚注 10 の CAlg 版：弱終対象 U の Čech 脈体 U_• と環の前層 O について、CAlg_A 値の RΓ(O) ≃ Tot_{E∞}(O(U_•))（E∞ 代数として）。
方針：S3 を E = CAlg_A で（`isLimitCone_iff_restrict_cech`）と `totEInfinity_isLimitCone`。
規約：O は層（Cor 3.12 の CAlg 版、`isSheaf_iff_forget`）。
使われ方：A2 の Δ_0 の CAlg 値 ＝ Čech–Alexander 模型の Tot_{E∞}。 -/
def derivedGlobalSectionsCAlg_eq_totEInfinity {𝒟 : Type u} [SmallCategory 𝒟]
    (J : GrothendieckTopology 𝒟) (hJ : _root_.SerrePositivity.InfinityCategories.Sheaves.Sheafification J (E.CAlg A)) (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A))
    (O : 𝒟ᵒᵖ ⥤ Under (CommRingCat.of A)) (hO : _root_.SerrePositivity.InfinityCategories.Sheaves.IsSheaf J (_root_.SerrePositivity.InfinityCategories.Sheaves.ringPresheafToCAlg (E := E) A O))
    (U : 𝒟) (hU : _root_.SerrePositivity.InfinityCategories.Sheaves.IsWeaklyTerminal U) (d : _root_.SerrePositivity.InfinityCategories.Sheaves.CechNerveData U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Sheaves.derivedGlobalSectionsCAlg (E := E) J A hJ hA (_root_.SerrePositivity.InfinityCategories.Sheaves.ringPresheafToCAlg (E := E) A O))
      (totEInfinity (E := E) A (d.obj.rightOp ⋙ O)) := by
  sorry -- S2 の層の RΓ と S3 で d に制限した錐を totEInfinity_isLimitCone と比較

/-! ## 厳密な自然変換から関手 ∞ 圏の辺へ（a1-design §10.5 の (ii)、11-07 追加）

小さい圏 𝒞（`Poly k` など、Type u）から大きい圏 𝒟（余単体的代数・cdga、Type (u+1)）への厳密な関手を、持ち上げた形状
`uliftFunctor.obj (nerve 𝒞)` からの単体集合の射にし、厳密な自然変換を実際の単体的ホモトピー（N(𝒞 × [1]) ≅ N𝒞 × Δ¹）にする。
∞ 関手 T : N𝒟 → X を後合成し、成分ごとに可逆なら本体の `functorIsoOfPointwiseInvertibleHomotopy`（Core/FunctorEdgePointwise）で
関手 ∞ 圏の同型を得る。 -/

section StrictNatTrans

variable {𝒞 : Type u} [SmallCategory 𝒞] {𝒟 𝒟' : Type (u+1)} [Category.{u} 𝒟] [Category.{u} 𝒟']

/-- 概要：小さい圏からの厳密な関手 F : 𝒞 ⥤ 𝒟 の、持ち上げた形状からの nerve の射。
方針：`formsNerve`（A1/CrystallineInput）と同じく、射列を F で写して `ULift.down` で読む。
規約：始域は `SSet.uliftFunctor.{u+1,u}.obj (nerve 𝒞)`（A2 の `polyUnderlying` と同じ形状）。
使われ方：a1-design §10.5 の大きい模型・小さい模型の関手を ∞ 関手にする。 -/
def strictShapeNerve (F : 𝒞 ⥤ 𝒟) : (SSet.uliftFunctor.{u+1,u}).obj (nerve 𝒞) ⟶ nerve 𝒟 where
  app _ := ↾fun q => (F.mapComposableArrows _).obj q.down
  naturality := by sorry -- 射列の制限と F による像の可換性（formsNerve と同じ）

/-- 概要：後合成との両立：strictShapeNerve (F ⋙ G) = strictShapeNerve F ≫ nerveMap G。
方針：射列の像の合成。
規約：等式（定義の展開で成り立つはず）。
使われ方：§10.5 の段 6（cdga の評価と `formsCAlg` の同一視）。 -/
theorem strictShapeNerve_comp (F : 𝒞 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒟') :
    strictShapeNerve (F ⋙ G) = strictShapeNerve F ≫ nerveMap G := by
  sorry -- 両辺とも射列 q ↦ (F ⋙ G).mapComposableArrows q。mapComposableArrows の合成則

/-- 概要：厳密な自然変換 α : F ⟶ G は持ち上げた nerve の間の実際の単体的ホモトピーを与える（N(𝒞 × [1]) ≅ N𝒞 × Δ¹）。
方針：本体の `SerrePositivity.NerveHomotopy.homotopy`（HomotopicalAlgebra/Simplicial/NerveHomotopy、同じ宇宙の圏）を
`ULiftHom (ULift 𝒞)` に当て、`strictShapeNerve` と同一視する。
規約：時刻 0 で F、時刻 1 で G。
使われ方：`strictNatTransFunctorIso`、A1-5 の `baseChangeTotHomotopy`。 -/
def strictNatTransHomotopy {F G : 𝒞 ⥤ 𝒟} (α : F ⟶ G) :
    SSet.Homotopy (strictShapeNerve F) (strictShapeNerve G) := by
  sorry -- NerveHomotopy.homotopy (ULiftHom.up 経由の α) を持ち上げた形状へ移す

/-- 概要：単体的ホモトピーの後合成。
方針：h ≫ T。端点は h₀・h₁ と結合律。
規約：本体の前合成 `stableHomotopyPrecomp`（Core/HomotopyPrecomposition）と対。
使われ方：`strictNatTransFunctorIso`。 -/
def homotopyPostcomp {X Y Z : SSet.{u+1}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) (T : Y ⟶ Z) :
    SSet.Homotopy (f ≫ T) (g ≫ T) where
  h := H.h ≫ T
  h₀ := by
    change SSet.ι₀ ≫ (H.h ≫ T) = f ≫ T
    simpa only [Category.assoc] using congrArg (fun k => k ≫ T) H.h₀
  h₁ := by
    change SSet.ι₁ ≫ (H.h ≫ T) = g ≫ T
    simpa only [Category.assoc] using congrArg (fun k => k ≫ T) H.h₁
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

/-- 概要：厳密な自然変換 α : F ⟶ G と ∞ 関手 T : N𝒟 → X について、各成分の像 T(α_c) が可逆なら関手 ∞ 圏の同型
strictShapeNerve F ≫ T ≅ strictShapeNerve G ≫ T（a1-design §10.5 の (ii)＋(iii)）。
方針：`homotopyPostcomp (strictNatTransHomotopy α) T` に本体の `functorIsoOfPointwiseInvertibleHomotopy` を当てる。
頂点 c での辺は nerve の辺 α_c の T による像（`simplicialHomotopyVertexEdge` の計算）。
規約：同型の順方向はホモトピーの辺の類。
使われ方：A1-5 の段 5・6（`smallFrame`・`pdDeRhamProjection` の比較）。 -/
def strictNatTransFunctorIso {X : SSet.{u+1}} [Quasicategory X] {F G : 𝒞 ⥤ 𝒟} (α : F ⟶ G)
    (T : nerve 𝒟 ⟶ X)
    (hα : ∀ c : 𝒞, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (α.app c)).map T).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (strictShapeNerve F ≫ T) (strictShapeNerve G ≫ T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (homotopyPostcomp (strictNatTransHomotopy α) T) (by
    sorry) -- 頂点 ULift.up (nerveVertex c) での辺は (nerve.edgeMk (α.app c)).map T。hα c で可逆

end StrictNatTrans

/-! ## 余単体的 cdga の Tot（a1-design §10.5 の段 6、11-07 追加） -/

section CosimplicialCDGA

open SerrePositivity.EInfinity SerrePositivity.DifferentialGraded

/-- 概要：余単体的 cdga（余単体的対象 [n] ↦ CommMon(Complex A)）。例：Ω^•_pd(D^n)。
方針：Mathlib の `CosimplicialObject`。
規約：Complex A は ℤ 次数の余鎖複体（DifferentialGraded）。
使われ方：A1-5 の `pdDeRhamCDGA`。 -/
abbrev CosimplicialCDGA := CosimplicialObject (CommMon (Complex A))

/-- 概要：厳密な cdga の CAlg_A への実現。
方針：nerve の後合成。
規約：—
使われ方：`totCDGA_evalZero`、A1 の `formsCAlg_eq`。 -/
def cdgaCAlg : nerve (CommMon (Complex A)) ⟶ E.CAlg A := E.ofCdga A

/-- 概要：可換 A 代数を次数 0 の cdga とみる関手。
方針：界面の厳密入力と同じ次数 0 の single 複体。
規約：微分は零。
使われ方：`totCDGA_discrete`、A1-5 の `pdDeRhamProjection`。 -/
def discreteCDGA : Under (CommRingCat.of A) ⥤ CommMon (Complex A) := SerrePositivity.EInfinity.discreteCDGA A

/-- 概要：余単体的 cdga の Tot_{E∞}：余単体的 cdga を CAlg_A の Δ 上の極限に送る関手。
方針：`totEInfinityFunctor` と同じ構成を、各項が cdga の場合へ（Berger–Fresse の余単体的 E∞ 代数の Tot）。CAlg_A の Δ 上の極限としても特徴づく。
規約：下の複体は総複体（交代余面 × 形式の微分、標準の符号）。
使われ方：A1-5 の段 6。基盤待ち（`totEInfinityFunctor` と同じ）。 -/
def totCDGAFunctor : nerve (CosimplicialCDGA A) ⟶ E.CAlg A := E.ofCosimplicialCdga A

/-- 概要：次数 0 の cdga からなる余単体的対象では、cdga の Tot は余単体的可換環の Tot に一致（関手として）。
方針：形式の方向が次数 0 だけなので総複体は交代余面複体、E∞ 構造も同じ構成。
規約：関手 ∞ 圏の同型。
使われ方：A1-5 の段 6（`pdDeRhamFunctorIso`）。 -/
def totCDGA_discrete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (discreteCDGA A)) ≫ totCDGAFunctor (E := E) A)
      (totEInfinityFunctor (E := E) A) := E.ofCosimplicialCdga_discrete A

/-- 概要：Tot から第 0 項への射影：cdga の Tot から [0] での値への自然な辺（CAlg_A の Δ 上の極限錐の [0] の脚）。
鎖のレベルでは総複体の列 n = 0 への射影（交代余面の微分は列の番号を上げるので鎖写像、AW 積の前面は [0] で積を保つ）。
方針：`totEInfinityCone` の [0] の脚を cdga について関手化する。
規約：時刻 0 で Tot、時刻 1 で ev_[0] ≫ cdgaCAlg。
使われ方：A1-5 の段 6（Tot K → K^0 = Ω^•）。 -/
def totCDGA_evalZero :
    SSet.Homotopy (totCDGAFunctor (E := E) A) (nerveMap ((evaluation SimplexCategory (CommMon (Complex A))).obj ⦋0⦌) ≫ cdgaCAlg (E := E) A) := E.ofCosimplicialCdga_evalZero A

/-- 概要：ホモトピー的に定数な余単体的 cdga（全ての構造射が下の複体の擬同型）では、第 0 項への射影は可逆。
方針：Δ は弱可縮なので、全ての射が同値の図式の極限錐の脚は同値。鎖のレベルでは列についてのスペクトル系列（E_1 は H(X^0) の定数余単体的
加群の交代余面複体で、n ≥ 1 は完全）。
規約：仮定は全ての θ について `QuasiIso`。
使われ方：A1-5 の段 6（pd Poincaré `pdPoincare_column` の一般の k 版から）。 -/
theorem totCDGA_evalZero_isInvertible (X : CosimplicialCDGA A)
    (hX : ∀ {m n : SimplexCategory} (θ : m ⟶ n), QuasiIso (X.map θ).hom.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (totCDGA_evalZero (E := E) A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)).toTruncated := by
  sorry -- 定数図式との比較（全ての余面が H で同じ同型）。E_1 の列 n ≥ 1 は完全、列 0 だけが残る

end CosimplicialCDGA

/-! ## Tot と係数制限（a1-design §10.5 の段 3・4 の随伴の転置、11-07 追加） -/

/-- 概要：余単体的代数の係数制限（各項で Under.map g）。
方針：`Under.map` の後合成。
規約：g : A → B に沿って B 代数を A 代数とみる。
使われ方：A1-5 の `wittBigBridge`（ψ）・`wittToSmall`（w₀）。 -/
abbrev restrictCosimplicial {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    CosimplicialAlgebra B ⥤ CosimplicialAlgebra A :=
  (Functor.whiskeringRight SimplexCategory _ _).obj (Under.map (CommRingCat.ofHom g))

/-- 概要：Tot_{E∞} は係数制限と可換（関手として）：res_g ∘ Tot_B ≅ Tot_A ∘ res_g。
方針：界面の全関手比較を用いる。
規約：関手 ∞ 圏の同型。DerivedGeneral/ScalarRestriction の `cAlgRestrictScalars`。
使われ方：A1-5 の `baseChangeTotHomotopy`（随伴の転置）。 -/
def totEInfinity_restrict {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (restrictCosimplicial g) ≫ totEInfinityFunctor (E := E) A)
      (totEInfinityFunctor (E := E) B ≫ SerrePositivity.InfinityCategories.cAlgRestrictScalars (E := E) g) := E.ofCosimplicial_restrict g

end SerrePositivity.Cosimplicial
