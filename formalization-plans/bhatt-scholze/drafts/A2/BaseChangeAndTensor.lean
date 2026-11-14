-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.BaseChange（仮。原典 Construction 7.6 の (4)(5) と D32）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.4、単位 A2-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdges

-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology,HodgeTateFiltration}.lean、drafts/DerivedGeneral/CompletionFunctor.lean、
-- drafts/A1/HodgeTateComparison.lean（Cor 4.12）、drafts/A7/AnimatedDomain.lean、drafts/DerivedGeneral/ScalarRestriction.lean を import する。

/-!
# 導来 prismatic コホモロジーの底変換・テンソル・導来 p 完備化不変性（BS 著者版 Construction 7.6 の (4)(5)）

## 概要
(4) 有界 prism の射 (A,(d)) → (A′,(d′)) について Δ_{R_{A′}/A′} ≃ Δ_{R/A} ⊗̂^L_A A′（完備底変換）。(5) Δ は sifted 余極限を保ち（構成）、
有限余積（テンソル）を完備テンソルへ送る：Δ_{R ⊗^L_k R′} ≃ Δ_R ⊗̂ Δ_{R′}（E∞ 代数の余積）。これが「対称モノイダル」の内容。
D32：Δ_R は R の導来 p 完備化で不変。

## 方針
いずれも Poly 上で示して Kan 延長（両辺が sifted 余極限を保つ）で一般へ。(4) の Poly 上は Cor 4.12（A1）。(5) の Poly 上は多項式代数の
Künneth：HT filtration つきの比較射 Δ_{P⊗P′} ← Δ_P ⊗̂ Δ_{P′} が gr で Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′} の同型を誘導し、filtration が
exhaustive・完備なので同型。D32 も gr（余接複体の p 完備化の不変性）と導来 Nakayama。

## 規約
完備テンソル・完備底変換は DerivedGeneral/CompletionFunctor の `completedBaseChange`。E∞ 代数の余積 ＝ テンソル（HA 3.2.4.7、G-A2-4）。

## 使われ方
A5（Prop 8.5 の底変換）、A7（Prop 8.13：S ↦ S_perfd の対称モノイダル性は (5) の Frobenius 余極限と完備化への移送）、A8（Thm 10.11）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity SerrePositivity.BhattScholze.Perfectoidization.Derived
-- animatedCompletion と completeDiscreteToAnimated は A2-1 だけに依存する A7/AnimatedDomain の定義。

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## (4) 底変換 -/

/-- 係数を g で送り、多項式準同型を各変数の像から延長する。 -/
abbrev polyScalarExtension {k k' : Type u} [CommRing k] [CommRing k'] (g : k →+* k') :
    Poly k ⥤ Poly k' := changePoly g

def animatedScalarExtension {k k' : Type u} [CommRing k] [CommRing k'] (g : k →+* k') :=
  siftedLan k (animatedAlgebra_siftedColimits k').1
    ((SSet.uliftFunctor.{u+1,u}).map (nerveMap (polyScalarExtension g)) ≫ polyYoneda k')

def animatedScalarRestriction {k k' : Type u} [CommRing k] [CommRing k'] (g : k →+* k') :
    AnimatedAlgebra k' ⟶ AnimatedAlgebra k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion _ ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityRestriction (nerveMap (polyScalarExtension g))) (by
      sorry) -- polyScalarExtension は変数の併置・空族を保存する

/-- π₀ の反射を導来 p 完備な代数に制限する。単位は X → π₀X。 -/
def completePiZeroReflection (k : Type u) [CommRing k] :
    Σ L : CompleteAnimatedAlgebra p k ⟶ nerve (PerfectoidizationInterface.C_R k p),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (completeDiscreteToAnimated p k) := by
  sorry -- animatedPiZeroAdjunction の制限。導来 p 完備な複体の各ホモロジー加群は導来 p 完備
/-- 完備 R 代数から、P/d≃R で底を読み替えた Δ。A7 の animatedDelta の入口。 -/
def deltaOverQuotientIso {R : Type u} [CommRing R] (e : A ⧸ P.ideal ≃+* R) :
    CompleteAnimatedAlgebra p R ⟶ CompleteCAlg (E := E) P :=
  animatedCompleteInclusion p R ≫ animatedScalarExtension e.symm.toRingHom ≫ derivedPrismaticCohomology (E := E) P hP

/-- 概要：prism の射 f : (A,(d)) → (A′,(d′)) に沿う始域の底変換 R ↦ R ⊗^L_k k′（P_Σ の関手。Poly 上は多項式代数の底変換で、sifted 余極限保存な延長）。
方針：Poly k → Poly k′（同じ添字 n）の nerve を P_Σ へ延長。
規約：k′ = A′/d′。
使われ方：(4) の主張。 -/
def animatedBaseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A') (f : OrientedPrism.Hom P P') :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ AnimatedAlgebra (A' ⧸ P'.ideal) :=
  animatedScalarExtension f.quotientMap

def completedPrismBaseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (f : OrientedPrism.Hom P P') : CompleteCAlg (E := E) P ⟶ CompleteCAlg (E := E) P' :=
  prismCompleteInclusion (E := E) P ≫ cAlgBaseChange (E := E) f.toRingHom ≫ prismCompletion (E := E) P'

/-- 概要：(4)：Δ_{R_{A′}/A′} ≃ Δ_{R/A} ⊗̂^L_A A′（完備底変換、E∞ 代数として）。
方針：Poly 上は Cor 4.12（`prismaticCohomology_baseChange'`、Tor 振幅の仮定なし）。両辺とも sifted 余極限保存（完備底変換は左随伴の合成）。
規約：同値は 𝒱 の可逆な辺、R について自然。
使われ方：A5、A7、A8。 -/
def derivedPrismaticCohomology_baseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedPrismaticCohomology (E := E) P hP ≫ completedPrismBaseChange (E := E) P P' f)
      (animatedBaseChange P P' f ≫ derivedPrismaticCohomology (E := E) P' hP') := by
  sorry -- Cor 4.12 の多項式上の標準比較を siftedRestriction_equivalence に沿って延長

/-- G-A2-10 の比較。完備底変換の単位、(4)、T ⊗_k k′ → T の乗法の順。 -/
def perfectBaseComparison {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (animatedScalarRestriction f.quotientMap ≫ deltaUnderlying (E := E) P hP)
      (deltaUnderlying (E := E) P' hP' ≫ cAlgRestrictScalars (E := E) f.toRingHom) := by
  sorry -- 要確認：ScalarRestriction へ。cAlgBaseChange_restrictScalars_adjunction の単位、
        -- derivedPrismaticCohomology_baseChange と animated な底変換の余単位の合成

theorem perfectBaseComparison_isIso {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P')
    (_ : P.deltaStructure.IsPerfect) (_ : P'.deltaStructure.IsPerfect)
    (T : PerfectoidizationInterface.A_R (A' ⧸ P'.ideal)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (perfectBaseComparison (E := E) P hP P' hP' f)
      ((discreteToAnimated _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T))) := by
  sorry -- 完全 prism の商間では相対完備余接複体が零。HT の gr、exhaustive 性、導来 Nakayama

/-! ## (5) sifted 余極限とテンソル -/

/-- 概要：Δ は sifted 余極限を保つ（構成から）。
方針：`derivedPrismaticCohomology_preservesSifted`。
規約：𝒱 の sifted 余極限 ＝ CAlg_A の sifted 余極限の完備化。
使われ方：(5)。 -/
theorem derivedPrismaticCohomology_siftedColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits (derivedPrismaticCohomology (E := E) P hP) :=
  derivedPrismaticCohomology_preservesSifted (E := E) P hP

/-- 概要：多項式代数の Künneth（Poly 上の (5)）：Δ_{P ⊗ P′} ≃ Δ_P ⊗̂ Δ_{P′}。
方針：比較射は E∞ 代数の余積の普遍性（Δ_P → Δ_{P⊗P′} ← Δ_{P′}、関手性）。gr で Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′}（Shared/DeRhamPolynomial）、
filtration は exhaustive・有限段、完備性。または Čech–Alexander 模型と Eilenberg–Zilber。
規約：—
使われ方：(5) の一般へ。 -/
def polyTensorCocone {k : Type u} [CommRing k] (n m : ℕ) :=
  let c := polyCofan k ⟨n⟩ ⟨m⟩
  let D := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⟨n⟩ : Poly k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⟨m⟩ : Poly k))
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges D (z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt)
    (by
      dsimp only [D, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft]
      rw [CategoryTheory.Limits.coprod.inl_desc, Equiv.apply_symm_apply]
      convert (nerve.edgeMk c.inl).toTruncated using 1 <;> rfl)
    (by
      dsimp only [D, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight]
      rw [CategoryTheory.Limits.coprod.inr_desc, Equiv.apply_symm_apply]
      convert (nerve.edgeMk c.inr).toTruncated using 1 <;> rfl)

theorem prismaticCohomologyPoly_tensor (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (prismaticCohomologyPolyFunctor (E := E) P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u,u+1} (polyTensorCocone (k := A ⧸ P.ideal) n m))) := by
  sorry -- 標準の二つの変数包含を脚とする比較を HT の gr で検出。微分形式の Künneth と有限 filtration

/-- 概要：(5)：Δ_{R ⊗^L_k R′} ≃ Δ_R ⊗̂ Δ_{R′}（𝒱 の余積）。すなわち Δ は対称モノイダル。
方針：両辺が各変数で sifted 余極限を保つ（P_Σ のテンソルは各変数で sifted 余極限を保つ、HTT 5.5.8.？）ので、Poly 上の Künneth から。
規約：対称性・結合性の coherence は E∞ 代数の余積のもの。
使われ方：Prop 8.13（A7）、Thm 10.11。 -/
theorem derivedPrismaticCohomology_tensor (X Y : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram X Y)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (derivedPrismaticCohomology (E := E) P hP) c) := by
  -- 証明の手順（D78、BS-W16 §28.2）：
  -- 1. 出力の E.coprodWith_cocone A (Δ X) (Δ Y) の普遍性で、同じ二脚を持つ
  --    Δ c.vertex への比較辺 q を作る。頂点ごとの任意の同型を選び直さない。
  -- 2. E.coproduct_tensor A (Δ Y) で U(q) の始域を導来テンソルへ移し、
  --    E.coproduct_tensor_legs A (Δ X) (Δ Y) で二脚を標準テンソル射へ同定する。
  -- 3. 多項式の場合は、その同じ射を HT の gr と微分形式の Künneth で検出する
  --    prismaticCohomologyPoly_tensor を使う。全関手版の比較の自然性と各変数の
  --    多項式 sifted 表示で余極限を交換し、一般の X, Y の U(q) も同値と示す。
  -- 4. E.forget_conservative で q が可逆と戻す。二点離散図式の余錐についての
  --    一般の移送補題（頂点の同値とホモトピー圏での二脚の一致）で、
  --    指定余積錐から mapJoinCocone Δ c へ余極限性を移す。
  -- 注意：忘却後のテンソルと二脚が、D(A) の加法的余積錐だとは主張しない。
  sorry

/-- 空の余積も保つ。二項テンソルと合わせて有限余積の保存になる。 -/
theorem derivedPrismaticCohomology_initial {X : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((derivedPrismaticCohomology (E := E) P hP).app _ X) := by
  sorry -- 始対象は変数 0 の多項式。基底 prism がその site の始対象なので Δ_k=A

/-! ## D32：導来 p 完備化不変性 -/

/-- 概要：D32：animated な導来 p 完備化 R → LΛ_p R（A7-1 `animatedCompletion`）は Δ の同値 Δ_R ≃ Δ_{LΛ_p R} を誘導する。
方針：gr（`cotangentWedge`）の不変性（S = LΛ_p R で R/p^n → S/p^n 同値、L_{S/R}^∧ = 0、推移三角）、exhaustive 性（完備圏）、導来 Nakayama。
規約：**離散 R の `completionRing R` = H⁰(LΛ_p R) とは別**（W9-I-29：LΛ_p R は離散とは限らない。例 R = Z_p ⊕ Q_p/Z_p）。E3 の欄との接続は
perfd の段で Prop 8.5 の系 4（a5-design §7.1）。
使われ方：A7（Prop 8.13 の完備化）、A8（Thm 10.11 の filtered 余極限）。 -/
theorem derivedPrismaticCohomology_completion_animated (X : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌) :
    IsIso ((hoFunctor.map (derivedPrismaticCohomology (E := E) P hP)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (animatedCompletionUnit p (A ⧸ P.ideal)) X)) := by
  sorry -- X→LΛ_p X は導来 mod p^n で同値。完備相対余接複体の消滅から各 gr を比較し、
        -- 完備余極限と導来 Nakayama で同じ単位の Δ による像が可逆

end SerrePositivity.BhattScholze.Prismatic
